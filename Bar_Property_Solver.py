#!/usr/bin/env python3
"""
Bar Property Solver v1.0
========================
Per-structure thickness sweep for bar properties.
Groups bar properties by Structure Name, iterates through thickness range,
and reports combined stress variation per thickness.

No Allowable, no RF, no Optimization algorithms.
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
import os
import threading
import csv
import pandas as pd
from pyNastran.bdf.bdf import BDF
from pyNastran.op2.op2 import OP2
import numpy as np
import subprocess
from datetime import datetime
from scipy.optimize import curve_fit


class BarPropertySolver:
    def __init__(self, root):
        self.root = root
        self.root.title("Bar Property Solver v1.0")
        self.root.geometry("1300x950")

        # Input paths
        self.bdf_paths = []
        self.property_excel_path = tk.StringVar()
        self.element_excel_path = tk.StringVar()
        self.residual_strength_path = tk.StringVar()
        self.nastran_path = tk.StringVar()
        self.output_folder = tk.StringVar()

        # Thickness ranges
        self.bar_min_thickness = tk.StringVar(value="2.0")
        self.bar_max_thickness = tk.StringVar(value="12.0")
        self.thickness_step = tk.StringVar(value="0.5")

        # Data storage
        self.bdf_model = None
        self.bdf_models = []
        self.bar_properties = {}          # PID -> {'dim1': val, 'dim2': val}
        self.bar_structure_map = {}       # PID -> Structure Name
        self.structure_groups = {}        # Structure Name -> [PID list]
        self.skin_properties = {}         # PID -> {'thickness': val}
        self.pbarl_dims = {}              # PID -> {'dim1': val, 'dim2': val} from BDF
        self.current_bar_thicknesses = {} # PID -> thickness
        self.current_skin_thicknesses = {}# PID -> thickness
        self.original_bar_thicknesses = {} # PID -> original dim1 from BDF
        self.material_densities = {}      # MID -> density
        self.prop_to_material = {}        # PID -> MID
        self.element_areas = {}
        self.bar_lengths = {}
        self.prop_elements = {}
        self.elem_to_prop = {}
        self.element_centroids = {}
        self.bar_elements = []
        self.shell_elements = []
        self.residual_strength_df = None
        self.combination_table = []
        self.landing_elem_ids = []
        self.bar_offset_elem_ids = []

        # Run state
        self.is_running = False
        self.sweep_results = {}  # Structure Name -> [{thickness, stresses, ...}]

        self.setup_ui()

    # ==================== GUI ====================
    def setup_ui(self):
        canvas = tk.Canvas(self.root)
        scrollbar = ttk.Scrollbar(self.root, orient="vertical", command=canvas.yview)
        scrollable_frame = ttk.Frame(canvas)
        scrollable_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        main = scrollable_frame

        ttk.Label(main, text="Bar Property Solver v1.0", font=('Helvetica', 16, 'bold')).pack(pady=10)
        ttk.Label(main, text="Per-structure thickness sweep with combined stress output", foreground='gray').pack()

        # ---- Section 1: Input Files ----
        f1 = ttk.LabelFrame(main, text="1. Input Files", padding=10)
        f1.pack(fill=tk.X, pady=5, padx=10)

        # Multi-BDF selection
        bdf_frame = ttk.Frame(f1)
        bdf_frame.pack(fill=tk.X, pady=2)
        ttk.Label(bdf_frame, text="BDF Files:", width=18).pack(side=tk.LEFT, anchor=tk.N)

        bdf_list_frame = ttk.Frame(bdf_frame)
        bdf_list_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.bdf_listbox = tk.Listbox(bdf_list_frame, height=3, width=55, selectmode=tk.SINGLE)
        self.bdf_listbox.pack(side=tk.LEFT, fill=tk.X, expand=True)
        bdf_scroll = ttk.Scrollbar(bdf_list_frame, orient="vertical", command=self.bdf_listbox.yview)
        bdf_scroll.pack(side=tk.LEFT, fill=tk.Y)
        self.bdf_listbox.configure(yscrollcommand=bdf_scroll.set)

        bdf_btn_frame = ttk.Frame(bdf_frame)
        bdf_btn_frame.pack(side=tk.LEFT, padx=5)
        ttk.Button(bdf_btn_frame, text="Add", command=self.add_bdf).pack(fill=tk.X, pady=1)
        ttk.Button(bdf_btn_frame, text="Remove", command=self.remove_bdf).pack(fill=tk.X, pady=1)
        ttk.Button(bdf_btn_frame, text="Load All", command=self.load_bdf).pack(fill=tk.X, pady=1)

        self.bdf_status = ttk.Label(f1, text="No BDF files loaded", foreground="gray")
        self.bdf_status.pack(anchor=tk.W)

        # Property Excel
        self._add_file_row(f1, "Property Excel:", self.property_excel_path, self.load_properties)
        self.prop_status = ttk.Label(f1, text="Not loaded", foreground="gray")
        self.prop_status.pack(anchor=tk.W)

        # Residual Strength
        self._add_file_row(f1, "Residual Strength:", self.residual_strength_path, self.load_residual_strength)
        self.resid_status = ttk.Label(f1, text="Not loaded", foreground="gray")
        self.resid_status.pack(anchor=tk.W)

        # Offset Element IDs
        self._add_file_row(f1, "Offset Element IDs:", self.element_excel_path, self.load_element_ids)
        self.elem_status = ttk.Label(f1, text="Not loaded", foreground="gray")
        self.elem_status.pack(anchor=tk.W)

        # Nastran Exe
        nast_frame = ttk.Frame(f1)
        nast_frame.pack(fill=tk.X, pady=2)
        ttk.Label(nast_frame, text="Nastran Exe:", width=18).pack(side=tk.LEFT)
        ttk.Entry(nast_frame, textvariable=self.nastran_path, width=45).pack(side=tk.LEFT, padx=5)
        ttk.Button(nast_frame, text="Browse", command=lambda: self.nastran_path.set(
            filedialog.askopenfilename(filetypes=[("Executable", "*.exe"), ("All", "*.*")])
        )).pack(side=tk.LEFT)

        # Output Folder
        out_frame = ttk.Frame(f1)
        out_frame.pack(fill=tk.X, pady=2)
        ttk.Label(out_frame, text="Output Folder:", width=18).pack(side=tk.LEFT)
        ttk.Entry(out_frame, textvariable=self.output_folder, width=45).pack(side=tk.LEFT, padx=5)
        ttk.Button(out_frame, text="Browse", command=lambda: self.output_folder.set(
            filedialog.askdirectory()
        )).pack(side=tk.LEFT)

        # ---- Section 2: Thickness Ranges ----
        f2 = ttk.LabelFrame(main, text="2. Thickness Ranges (mm)", padding=10)
        f2.pack(fill=tk.X, pady=5, padx=10)

        row1 = ttk.Frame(f2)
        row1.pack(fill=tk.X, pady=2)
        ttk.Label(row1, text="Bar:  Min:").pack(side=tk.LEFT)
        ttk.Entry(row1, textvariable=self.bar_min_thickness, width=8).pack(side=tk.LEFT, padx=5)
        ttk.Label(row1, text="Max:").pack(side=tk.LEFT)
        ttk.Entry(row1, textvariable=self.bar_max_thickness, width=8).pack(side=tk.LEFT, padx=5)

        row2 = ttk.Frame(f2)
        row2.pack(fill=tk.X, pady=2)
        ttk.Label(row2, text="Step:").pack(side=tk.LEFT)
        ttk.Entry(row2, textvariable=self.thickness_step, width=8).pack(side=tk.LEFT, padx=5)

        # ---- Section 3: Actions ----
        f3 = ttk.LabelFrame(main, text="3. Actions", padding=10)
        f3.pack(fill=tk.X, pady=5, padx=10)

        btn_row = ttk.Frame(f3)
        btn_row.pack(fill=tk.X)
        self.btn_start = ttk.Button(btn_row, text=">>> START SWEEP", command=self.start_sweep)
        self.btn_start.pack(side=tk.LEFT, padx=5)
        self.btn_stop = ttk.Button(btn_row, text="STOP", command=self.stop_sweep, state=tk.DISABLED)
        self.btn_stop.pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_row, text="Clear Log", command=self.clear_log).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_row, text="Export", command=self.export_results).pack(side=tk.LEFT, padx=5)

        self.progress_var = tk.DoubleVar()
        self.progress_bar = ttk.Progressbar(f3, variable=self.progress_var, maximum=100)
        self.progress_bar.pack(fill=tk.X, pady=5)

        # ---- Section 4: Structure Groups ----
        f4 = ttk.LabelFrame(main, text="4. Structure Groups (from Property Excel)", padding=10)
        f4.pack(fill=tk.X, pady=5, padx=10)

        self.group_text = scrolledtext.ScrolledText(f4, height=6, width=100, state=tk.DISABLED)
        self.group_text.pack(fill=tk.X)

        # ---- Section 5: Log ----
        f5 = ttk.LabelFrame(main, text="5. Log", padding=10)
        f5.pack(fill=tk.BOTH, expand=True, pady=5, padx=10)

        self.log_text = scrolledtext.ScrolledText(f5, height=20, width=100)
        self.log_text.pack(fill=tk.BOTH, expand=True)

    def _add_file_row(self, parent, label, var, load_cmd):
        frame = ttk.Frame(parent)
        frame.pack(fill=tk.X, pady=2)
        ttk.Label(frame, text=label, width=18).pack(side=tk.LEFT)
        ttk.Entry(frame, textvariable=var, width=45).pack(side=tk.LEFT, padx=5)
        ttk.Button(frame, text="Browse", command=lambda: var.set(
            filedialog.askopenfilename(filetypes=[("Excel", "*.xlsx *.xls"), ("All", "*.*")])
        )).pack(side=tk.LEFT)
        ttk.Button(frame, text="Load", command=load_cmd).pack(side=tk.LEFT, padx=2)

    def log(self, msg):
        def _do():
            self.log_text.insert(tk.END, msg + "\n")
            self.log_text.see(tk.END)
        self.root.after(0, _do)

    def clear_log(self):
        self.log_text.delete(1.0, tk.END)

    # ==================== BDF FILE OPS ====================
    def add_bdf(self):
        paths = filedialog.askopenfilenames(filetypes=[("BDF", "*.bdf *.dat *.nas"), ("All", "*.*")])
        for p in paths:
            if p not in self.bdf_paths:
                self.bdf_paths.append(p)
                self.bdf_listbox.insert(tk.END, os.path.basename(p))
        self.bdf_status.config(text=f"{len(self.bdf_paths)} BDF files selected", foreground="blue")

    def remove_bdf(self):
        selection = self.bdf_listbox.curselection()
        if selection:
            idx = selection[0]
            self.bdf_listbox.delete(idx)
            del self.bdf_paths[idx]
        self.bdf_status.config(text=f"{len(self.bdf_paths)} BDF files selected", foreground="blue")

    # ==================== BDF LOADING ====================
    def load_bdf(self):
        if not self.bdf_paths:
            messagebox.showerror("Error", "Add at least one BDF file")
            return

        self.log("\n" + "=" * 70)
        self.log("LOADING BDF FILES")
        self.log("=" * 70)
        self.log(f"  BDF files to load: {len(self.bdf_paths)}")
        for i, p in enumerate(self.bdf_paths):
            self.log(f"    {i + 1}. {os.path.basename(p)}")

        try:
            path = self.bdf_paths[0]
            self.log(f"\n  Loading main BDF: {os.path.basename(path)}")
            self.bdf_model = BDF(debug=False)
            self.bdf_model.read_bdf(path, validate=False, xref=True, read_includes=True, encoding='latin-1')

            self.bdf_models = []
            for bdf_path in self.bdf_paths:
                self.log(f"  Loading: {os.path.basename(bdf_path)}")
                model = BDF(debug=False)
                model.read_bdf(bdf_path, validate=False, xref=True, read_includes=True, encoding='latin-1')
                self.bdf_models.append({'path': bdf_path, 'model': model, 'name': os.path.basename(bdf_path)})

            self.log(f"  Nodes: {len(self.bdf_model.nodes)}")
            self.log(f"  Elements: {len(self.bdf_model.elements)}")
            self.log(f"  Properties: {len(self.bdf_model.properties)}")
            self.log(f"  Materials: {len(self.bdf_model.materials)}")

            # Extract material densities
            self.material_densities = {}
            for mid, mat in self.bdf_model.materials.items():
                rho = None
                if hasattr(mat, 'rho') and mat.rho is not None:
                    rho = mat.rho
                elif hasattr(mat, 'Rho') and mat.Rho is not None:
                    rho = mat.Rho()
                if rho:
                    self.material_densities[mid] = rho
                    self.log(f"    Material {mid} ({mat.type}): density = {rho}")

            # Property -> Material mapping
            self.prop_to_material = {}
            for pid, prop in self.bdf_model.properties.items():
                mid = None
                if hasattr(prop, 'mid') and prop.mid:
                    mid = prop.mid if isinstance(prop.mid, int) else prop.mid.mid
                elif hasattr(prop, 'mid1') and prop.mid1:
                    mid = prop.mid1 if isinstance(prop.mid1, int) else prop.mid1.mid
                elif hasattr(prop, 'mid_ref') and prop.mid_ref:
                    mid = prop.mid_ref.mid
                if mid:
                    self.prop_to_material[pid] = mid

            # Element geometry
            self.element_areas = {}
            self.bar_lengths = {}
            self.prop_elements = {}
            self.elem_to_prop = {}
            self.element_centroids = {}
            self.bar_elements = []
            self.shell_elements = []

            shell_count = bar_count = 0
            for eid, elem in self.bdf_model.elements.items():
                pid = elem.pid if hasattr(elem, 'pid') else None
                if pid:
                    self.elem_to_prop[eid] = pid
                    if pid not in self.prop_elements:
                        self.prop_elements[pid] = []
                    self.prop_elements[pid].append(eid)

                try:
                    centroid = elem.Centroid()
                    self.element_centroids[eid] = centroid
                except:
                    pass

                if elem.type in ['CQUAD4', 'CTRIA3', 'CQUAD8', 'CTRIA6']:
                    shell_count += 1
                    self.shell_elements.append(eid)
                    try:
                        self.element_areas[eid] = elem.Area()
                    except:
                        self.element_areas[eid] = 0
                elif elem.type in ['CBAR', 'CBEAM']:
                    bar_count += 1
                    self.bar_elements.append(eid)
                    try:
                        self.bar_lengths[eid] = elem.Length()
                    except:
                        self.bar_lengths[eid] = 0

            # Extract PBARL dimensions from BDF
            self.pbarl_dims = {}
            for pid, prop in self.bdf_model.properties.items():
                if prop.type == 'PBARL':
                    dims = prop.dim if hasattr(prop, 'dim') else []
                    if len(dims) >= 2:
                        self.pbarl_dims[pid] = {'dim1': dims[0], 'dim2': dims[1]}
                    elif len(dims) == 1:
                        self.pbarl_dims[pid] = {'dim1': dims[0], 'dim2': dims[0]}

            # Store original dim1 from BDF as the original thicknesses
            self.original_bar_thicknesses = {}
            if self.pbarl_dims:
                self.log(f"  PBARL dimensions extracted: {len(self.pbarl_dims)} properties")
                for pid, d in self.pbarl_dims.items():
                    self.original_bar_thicknesses[pid] = d['dim1']
                    self.log(f"    PID {pid}: dim1={d['dim1']}, dim2={d['dim2']}")

            self.log(f"  Shells: {shell_count}, Bars: {bar_count}")
            self.log(f"  Centroids calculated: {len(self.element_centroids)}")
            self.log(f"\n  Total BDF models loaded: {len(self.bdf_models)}")

            self.bdf_status.config(
                text=f"Loaded: {len(self.bdf_models)} BDFs, {len(self.bdf_model.elements)} elements",
                foreground="green"
            )

            if not self.output_folder.get():
                self.output_folder.set(os.path.dirname(path))

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())
            self.bdf_status.config(text="Error", foreground="red")

    # ==================== PROPERTY LOADING ====================
    def load_properties(self):
        """Load Bar Property sheet with Bar Property ID and Structure Name columns."""
        path = self.property_excel_path.get()
        if not path:
            messagebox.showerror("Error", "Select Property Excel")
            return

        self.log("\n" + "=" * 70)
        self.log("LOADING PROPERTIES")
        self.log("=" * 70)

        try:
            xl = pd.ExcelFile(path)
            self.log(f"  Sheets: {xl.sheet_names}")

            bar_min = float(self.bar_min_thickness.get())

            self.bar_properties = {}
            self.bar_structure_map = {}
            self.structure_groups = {}
            self.skin_properties = {}
            self.current_bar_thicknesses = {}
            self.current_skin_thicknesses = {}

            for sheet in xl.sheet_names:
                sl = sheet.lower().replace('_', '').replace(' ', '')

                if 'bar' in sl and 'prop' in sl:
                    self.log(f"\n  Reading bar properties from '{sheet}'...")
                    df = pd.read_excel(xl, sheet_name=sheet)
                    self.log(f"    Columns: {list(df.columns)}")

                    # Find columns by name
                    pid_col = None
                    struct_col = None
                    for col in df.columns:
                        col_clean = str(col).lower().replace('_', '').replace(' ', '')
                        if 'barproperty' in col_clean or 'propertyid' in col_clean or col_clean == 'barpropid':
                            pid_col = col
                        elif 'structure' in col_clean or 'structurename' in col_clean:
                            struct_col = col

                    # Fallback to positional
                    if pid_col is None:
                        pid_col = df.columns[0]
                        self.log(f"    Using first column as PID: {pid_col}")
                    if struct_col is None and len(df.columns) > 1:
                        struct_col = df.columns[1]
                        self.log(f"    Using second column as Structure Name: {struct_col}")

                    self.log(f"    PID column: {pid_col}")
                    self.log(f"    Structure column: {struct_col}")

                    for _, row in df.iterrows():
                        pid_val = row[pid_col]
                        if pd.isna(pid_val):
                            continue
                        pid = int(pid_val)
                        struct_name = str(row[struct_col]).strip() if struct_col and pd.notna(row[struct_col]) else "DEFAULT"

                        # Use original BDF dim1 if available, otherwise bar_min
                        orig_dim1 = self.original_bar_thicknesses.get(pid, bar_min)
                        orig_dim2 = self.pbarl_dims[pid]['dim2'] if pid in self.pbarl_dims else bar_min

                        self.bar_properties[pid] = {
                            'dim1': orig_dim1,
                            'dim2': orig_dim2,
                        }
                        # Initialize to original BDF value (not bar_min)
                        self.current_bar_thicknesses[pid] = orig_dim1
                        self.bar_structure_map[pid] = struct_name

                        if struct_name not in self.structure_groups:
                            self.structure_groups[struct_name] = []
                        self.structure_groups[struct_name].append(pid)

                    self.log(f"  Loaded {len(self.bar_properties)} bar properties")
                    self.log(f"  Structure groups: {len(self.structure_groups)}")
                    for name, pids in sorted(self.structure_groups.items()):
                        self.log(f"    {name}: {len(pids)} properties")

                    # Log original thickness info
                    bdf_count = sum(1 for pid in self.bar_properties if pid in self.original_bar_thicknesses)
                    self.log(f"  Properties with BDF original dim1: {bdf_count}/{len(self.bar_properties)}")
                    self.log(f"  NOTE: Only active group thicknesses will change during sweep.")

                elif 'skin' in sl and 'prop' in sl:
                    self.log(f"\n  Reading skin properties from '{sheet}'...")
                    df = pd.read_excel(xl, sheet_name=sheet)
                    for _, row in df.iterrows():
                        pid = int(row.iloc[0]) if pd.notna(row.iloc[0]) else None
                        if pid:
                            skin_t = float(row.iloc[1]) if len(row) > 1 and pd.notna(row.iloc[1]) else 3.0
                            self.skin_properties[pid] = {'thickness': skin_t}
                            self.current_skin_thicknesses[pid] = skin_t
                    self.log(f"  Loaded {len(self.skin_properties)} skin properties")

            # Update group display
            self._update_group_display()

            total = len(self.bar_properties)
            groups = len(self.structure_groups)
            self.prop_status.config(
                text=f"Loaded: {total} bar props in {groups} groups, {len(self.skin_properties)} skin props",
                foreground="green"
            )

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())
            self.prop_status.config(text="Error", foreground="red")

    def _update_group_display(self):
        self.group_text.config(state=tk.NORMAL)
        self.group_text.delete(1.0, tk.END)
        for name in sorted(self.structure_groups.keys()):
            pids = self.structure_groups[name]
            pid_str = ", ".join(str(p) for p in sorted(pids)[:15])
            if len(pids) > 15:
                pid_str += f" ... (+{len(pids) - 15} more)"
            self.group_text.insert(tk.END, f"{name} ({len(pids)} props): {pid_str}\n")
        self.group_text.config(state=tk.DISABLED)

    # ==================== ELEMENT IDs (OFFSET) ====================
    def load_element_ids(self):
        path = self.element_excel_path.get()
        if not path:
            return

        self.log("\n" + "=" * 70)
        self.log("LOADING ELEMENT IDs FOR OFFSET")
        self.log("=" * 70)

        try:
            xl = pd.ExcelFile(path)
            self.landing_elem_ids = []
            self.bar_offset_elem_ids = []

            for s in xl.sheet_names:
                sl = s.lower().replace('_', '').replace(' ', '')
                df = pd.read_excel(xl, sheet_name=s)
                if 'landing' in sl:
                    self.landing_elem_ids = df.iloc[:, 0].dropna().astype(int).tolist()
                    self.log(f"  Landing: {len(self.landing_elem_ids)}")
                elif 'bar' in sl and 'offset' in sl:
                    self.bar_offset_elem_ids = df.iloc[:, 0].dropna().astype(int).tolist()
                    self.log(f"  Bar offset: {len(self.bar_offset_elem_ids)}")

            self.elem_status.config(
                text=f"Landing: {len(self.landing_elem_ids)}, Bar offset: {len(self.bar_offset_elem_ids)}",
                foreground="green"
            )

        except Exception as e:
            self.log(f"ERROR: {e}")
            self.elem_status.config(text="Error", foreground="red")

    # ==================== RESIDUAL STRENGTH ====================
    def load_residual_strength(self):
        path = self.residual_strength_path.get()
        if not path or not os.path.exists(path):
            messagebox.showerror("Error", "Select Residual Strength Excel file")
            return

        self.log("\n" + "=" * 70)
        self.log("LOADING RESIDUAL STRENGTH DATA")
        self.log("=" * 70)

        try:
            xl = pd.ExcelFile(path)
            self.log(f"  Sheets: {xl.sheet_names}")

            res_sh = None
            for sheet in xl.sheet_names:
                sl = sheet.lower().replace(' ', '').replace('_', '')
                if 'residual' in sl or 'strength' in sl:
                    res_sh = sheet
                    break

            if not res_sh:
                res_sh = xl.sheet_names[0]
                self.log(f"  No 'Residual Strength' sheet found, using: {res_sh}")
            else:
                self.log(f"  Found sheet: {res_sh}")

            self.residual_strength_df = pd.read_excel(xl, sheet_name=res_sh)
            self.log(f"  Loaded {len(self.residual_strength_df)} rows")
            self.log(f"  Columns: {list(self.residual_strength_df.columns)}")

            cols = self.residual_strength_df.columns.tolist()
            self.combination_table = []
            i = 1
            while i < len(cols) - 1:
                col_name = str(cols[i]).upper()
                next_col_name = str(cols[i + 1]).upper()
                if ('CASE' in col_name or 'ID' in col_name) and 'MULT' in next_col_name:
                    self.combination_table.append((cols[i], cols[i + 1]))
                    self.log(f"    Found pair: {cols[i]} + {cols[i + 1]}")
                    i += 2
                else:
                    i += 1

            self.log(f"  Total combination pairs: {len(self.combination_table)}")
            self.resid_status.config(
                text=f"{len(self.residual_strength_df)} rows, {len(self.combination_table)} pairs",
                foreground="green"
            )

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())
            self.resid_status.config(text="Error", foreground="red")

    # ==================== BDF WRITING ====================
    def _write_bdf_for_model(self, folder, model, original_path):
        output_bdf = os.path.join(folder, os.path.basename(original_path))

        with open(original_path, 'r', encoding='latin-1') as f:
            lines = f.readlines()

        new_lines = []
        i = 0
        while i < len(lines):
            line = lines[i]

            if line.startswith('PBARL'):
                try:
                    pid = int(line[8:16].strip())
                    if pid in self.current_bar_thicknesses:
                        t = self.current_bar_thicknesses[pid]
                        t = max(0.1, t)
                        new_lines.append(line)
                        i += 1
                        while i < len(lines) and (
                            lines[i].startswith('+') or lines[i].startswith('*') or
                            (lines[i][0] == ' ' and lines[i].strip() and not lines[i].strip().startswith('$'))
                        ):
                            cont = lines[i]
                            if cont.strip() and not cont.strip().startswith('$'):
                                try:
                                    original_dim2 = cont[16:24].strip()
                                    dim2_val = float(original_dim2) if original_dim2 else t
                                except:
                                    dim2_val = t
                                cont_name = cont[:8]
                                rest = cont[24:] if len(cont) > 24 else '\n'
                                new_cont = f"{cont_name}{t:8.4f}{dim2_val:8.4f}{rest}"
                                new_lines.append(new_cont)
                            else:
                                new_lines.append(cont)
                            i += 1
                        continue
                except:
                    pass

            elif line.startswith('PSHELL'):
                try:
                    pid = int(line[8:16].strip())
                    if pid in self.current_skin_thicknesses:
                        t = self.current_skin_thicknesses[pid]
                        t = max(0.1, t)
                        prefix = line[:16]
                        mid1 = line[16:24]
                        rest = line[32:] if len(line) > 32 else '\n'
                        new_line = f"{prefix}{mid1}{t:8.4f}{rest}"
                        new_lines.append(new_line)
                        i += 1
                        continue
                except:
                    pass

            new_lines.append(line)
            i += 1

        with open(output_bdf, 'w', encoding='latin-1') as f:
            f.writelines(new_lines)

        self.log(f"    BDF written: {os.path.basename(output_bdf)}")
        return output_bdf

    # ==================== OFFSET APPLICATION ====================
    def _apply_offsets(self, bdf_path, folder):
        if not self.landing_elem_ids and not self.bar_offset_elem_ids:
            self.log("    No offset elements defined, skipping")
            return bdf_path

        try:
            self.log(f"    Applying offsets...")
            bdf = BDF(debug=False)
            bdf.read_bdf(bdf_path, validate=False, xref=True, read_includes=True, encoding='latin-1')

            # Landing (shell) offsets: zoffset = -t/2
            landing_offsets = {}
            landing_normals = {}

            for eid in self.landing_elem_ids:
                if eid not in bdf.elements:
                    continue
                elem = bdf.elements[eid]
                pid = elem.pid if hasattr(elem, 'pid') else None
                if pid is None:
                    continue

                t = self.current_skin_thicknesses.get(pid, 3.0)
                t = max(0.1, t)
                landing_offsets[eid] = -t / 2.0

                if elem.type in ['CQUAD4', 'CTRIA3']:
                    try:
                        nids = elem.node_ids[:3]
                        nodes = [bdf.nodes[n] for n in nids if n in bdf.nodes]
                        if len(nodes) >= 3:
                            p1, p2, p3 = [np.array(n.get_position()) for n in nodes]
                            normal = np.cross(p2 - p1, p3 - p1)
                            nl = np.linalg.norm(normal)
                            if nl > 1e-10:
                                landing_normals[eid] = normal / nl
                    except:
                        pass

            self.log(f"    Landing offsets: {len(landing_offsets)} elements")

            # Node -> shell mapping for bar offset
            node_to_shells = {}
            for eid, elem in bdf.elements.items():
                if elem.type in ['CQUAD4', 'CTRIA3']:
                    for nid in elem.node_ids:
                        if nid not in node_to_shells:
                            node_to_shells[nid] = []
                        node_to_shells[nid].append(eid)

            # Bar offsets: WA = WB = -normal * (landing_t + bar_t/2)
            bar_offsets = {}
            for eid in self.bar_offset_elem_ids:
                if eid not in bdf.elements:
                    continue
                elem = bdf.elements[eid]
                if elem.type not in ['CBAR', 'CBEAM']:
                    continue

                pid = elem.pid if hasattr(elem, 'pid') else None
                if pid is None:
                    continue

                bar_t = self.current_bar_thicknesses.get(pid, float(self.bar_min_thickness.get()))
                bar_t = max(0.1, bar_t)

                bar_nodes = elem.node_ids[:2]
                if bar_nodes[0] in node_to_shells and bar_nodes[1] in node_to_shells:
                    common = set(node_to_shells[bar_nodes[0]]) & set(node_to_shells[bar_nodes[1]])
                    max_t = 0
                    best_normal = None

                    for shell_eid in common:
                        if shell_eid in landing_offsets:
                            shell_elem = bdf.elements[shell_eid]
                            shell_pid = shell_elem.pid if hasattr(shell_elem, 'pid') else None
                            if shell_pid:
                                shell_t = self.current_skin_thicknesses.get(shell_pid, 0)
                                if shell_t > max_t:
                                    max_t = shell_t
                                    if shell_eid in landing_normals:
                                        best_normal = landing_normals[shell_eid]

                    if best_normal is not None and max_t > 0:
                        offset_mag = max_t + bar_t / 2.0
                        bar_offsets[eid] = tuple(-best_normal * offset_mag)

            self.log(f"    Bar offsets: {len(bar_offsets)} elements")

            # Apply to BDF file
            with open(bdf_path, 'r', encoding='latin-1') as f:
                lines = f.readlines()

            def fmt(v, w=8):
                s = f"{v:.4f}"
                return s[:w].ljust(w) if len(s) <= w else f"{v:.2E}"[:w].ljust(w)

            new_lines = []
            i = 0
            applied_landing = 0
            applied_bar = 0

            while i < len(lines):
                line = lines[i]

                if line.startswith('CQUAD4'):
                    try:
                        eid = int(line[8:16].strip())
                        if eid in landing_offsets:
                            padded = line.rstrip().ljust(72)
                            new_line = padded[:64] + fmt(landing_offsets[eid]) + '\n'
                            new_lines.append(new_line)
                            applied_landing += 1
                            i += 1
                            continue
                    except:
                        pass

                elif line.startswith('CTRIA3'):
                    try:
                        eid = int(line[8:16].strip())
                        if eid in landing_offsets:
                            padded = line.rstrip().ljust(56)
                            new_line = padded[:48] + fmt(landing_offsets[eid]) + '\n'
                            new_lines.append(new_line)
                            applied_landing += 1
                            i += 1
                            continue
                    except:
                        pass

                elif line.startswith('CBAR'):
                    try:
                        eid = int(line[8:16].strip())
                        if eid in bar_offsets:
                            offset_vec = bar_offsets[eid]

                            if i + 1 < len(lines) and (
                                lines[i + 1].startswith('+') or lines[i + 1].startswith('*') or
                                (lines[i + 1][0] == ' ' and lines[i + 1].strip())
                            ):
                                cont_line = lines[i + 1]
                                if len(cont_line) < 24:
                                    cont_line = cont_line.rstrip().ljust(24)
                                new_cont = cont_line[:24]
                                new_cont += fmt(offset_vec[0])
                                new_cont += fmt(offset_vec[1])
                                new_cont += fmt(offset_vec[2])
                                new_cont += fmt(offset_vec[0])
                                new_cont += fmt(offset_vec[1])
                                new_cont += fmt(offset_vec[2])
                                new_cont += '\n'

                                new_lines.append(line)
                                new_lines.append(new_cont)
                                applied_bar += 1
                                i += 2
                                continue
                            else:
                                cont_name = '+CB' + str(eid)[-4:]
                                new_lines.append(line.rstrip() + cont_name + '\n')

                                new_cont = cont_name.ljust(8)
                                new_cont += '        '   # PA
                                new_cont += '        '   # PB
                                new_cont += fmt(offset_vec[0])
                                new_cont += fmt(offset_vec[1])
                                new_cont += fmt(offset_vec[2])
                                new_cont += fmt(offset_vec[0])
                                new_cont += fmt(offset_vec[1])
                                new_cont += fmt(offset_vec[2])
                                new_cont += '\n'
                                new_lines.append(new_cont)

                                applied_bar += 1
                                i += 1
                                continue
                    except:
                        pass

                new_lines.append(line)
                i += 1

            output_bdf = os.path.join(folder, "model_offset.bdf")
            with open(output_bdf, 'w', encoding='latin-1') as f:
                f.writelines(new_lines)

            self.log(f"    Offsets applied: {applied_landing} landing, {applied_bar} bar")
            return output_bdf

        except Exception as e:
            self.log(f"    Offset error: {e}")
            return bdf_path

    # ==================== NASTRAN EXECUTION ====================
    def _run_nastran(self, bdf_path, folder):
        nastran = self.nastran_path.get()
        if not nastran or not os.path.exists(nastran):
            self.log("    WARNING: Nastran exe not found!")
            return False
        try:
            cmd = f'"{nastran}" "{bdf_path}" out="{folder}" scratch=yes batch=no'
            proc = subprocess.Popen(cmd, shell=True)
            proc.wait(timeout=600)
            return True
        except:
            return False

    # ==================== STRESS EXTRACTION ====================
    def _extract_stresses(self, folder):
        results = []
        bar_stress_rows = []

        for f in os.listdir(folder):
            if f.lower().endswith('.op2'):
                op2_name = f
                try:
                    op2 = OP2(debug=False)
                    op2.read_op2(os.path.join(folder, f))

                    # BAR STRESS from cbar_force
                    if hasattr(op2, 'cbar_force') and op2.cbar_force:
                        for sc_id, force in op2.cbar_force.items():
                            for i, eid in enumerate(force.element):
                                axial = force.data[0, i, 6] if len(force.data.shape) == 3 else force.data[i, 6]
                                pid = self.elem_to_prop.get(int(eid))
                                d1 = d2 = area = stress = None

                                if pid and pid in self.bar_properties:
                                    d1 = self.current_bar_thicknesses.get(pid, self.bar_properties[pid].get('dim1', 0))
                                    if pid in self.pbarl_dims:
                                        d2 = self.pbarl_dims[pid]['dim2']
                                    else:
                                        d2 = self.bar_properties[pid].get('dim2', d1)
                                    area = d1 * d2
                                    if area > 0:
                                        stress = axial / area

                                results.append({
                                    'eid': int(eid), 'type': 'bar',
                                    'stress': float(stress) if stress else 0,
                                    'subcase': int(sc_id)
                                })

                                struct_name = self.bar_structure_map.get(pid, '') if pid else ''
                                bar_stress_rows.append({
                                    'OP2': op2_name, 'Subcase': int(sc_id), 'Element': int(eid),
                                    'Property': pid, 'Structure': struct_name,
                                    'Axial': float(axial) if axial else 0,
                                    'Dim1': d1, 'Dim2': d2, 'Area': area,
                                    'Stress': float(stress) if stress else None
                                })

                    # SHELL STRESS
                    shell_stress_attrs = [
                        ('cquad4_stress', 'CQUAD4'),
                        ('ctria3_stress', 'CTRIA3'),
                        ('cquad8_stress', 'CQUAD8'),
                        ('ctria6_stress', 'CTRIA6'),
                        ('cquad4_composite_stress', 'CQUAD4_COMP'),
                        ('ctria3_composite_stress', 'CTRIA3_COMP'),
                    ]

                    for attr_name, stress_type in shell_stress_attrs:
                        if hasattr(op2, attr_name):
                            stress_data = getattr(op2, attr_name)
                            if stress_data:
                                for sc_id, data in stress_data.items():
                                    for i, eid in enumerate(data.element):
                                        try:
                                            if len(data.data.shape) == 3:
                                                stress = data.data[0, i, -1]
                                            else:
                                                stress = data.data[i, -1]
                                            results.append({
                                                'eid': int(eid), 'type': 'shell',
                                                'stress': float(abs(stress)),
                                                'subcase': int(sc_id)
                                            })
                                        except:
                                            pass

                except Exception as e:
                    self.log(f"    OP2 read error: {e}")

        # Save bar stress CSV
        if bar_stress_rows:
            csv_path = os.path.join(folder, 'bar_stress_results.csv')
            with open(csv_path, 'w', newline='') as f:
                w = csv.DictWriter(f, fieldnames=[
                    'OP2', 'Subcase', 'Element', 'Property', 'Structure', 'Axial', 'Dim1', 'Dim2', 'Area', 'Stress'
                ])
                w.writeheader()
                w.writerows(bar_stress_rows)
            self.log(f"    Saved: bar_stress_results.csv ({len(bar_stress_rows)} rows)")

        return results

    # ==================== STRESS COMBINATION ====================
    def _combine_stresses_multi(self, folder, n_bdfs):
        if self.residual_strength_df is None or len(self.combination_table) == 0:
            return None

        try:
            all_stress_data = []
            if n_bdfs > 1:
                for item in os.listdir(folder):
                    subfolder = os.path.join(folder, item)
                    if os.path.isdir(subfolder) and item.startswith('bdf_'):
                        stress_csv = os.path.join(subfolder, 'bar_stress_results.csv')
                        if os.path.exists(stress_csv):
                            all_stress_data.append(pd.read_csv(stress_csv))
            else:
                stress_csv = os.path.join(folder, 'bar_stress_results.csv')
                if os.path.exists(stress_csv):
                    all_stress_data.append(pd.read_csv(stress_csv))

            if not all_stress_data:
                return None

            stress_df = pd.concat(all_stress_data, ignore_index=True)

            lookup = {}
            for _, row in stress_df.iterrows():
                key = (int(row['Subcase']), int(row['Element']))
                stress_val = row['Stress'] if pd.notna(row['Stress']) else 0
                if key not in lookup or abs(stress_val) > abs(lookup[key]):
                    lookup[key] = stress_val

            elements = stress_df['Element'].unique()
            rs_df = self.residual_strength_df
            cols = rs_df.columns.tolist()
            comb_col = cols[0]

            results = []
            for _, rs_row in rs_df.iterrows():
                comb_lc = rs_row[comb_col]
                if pd.isna(comb_lc):
                    continue
                comb_lc = int(comb_lc)

                for eid in elements:
                    total_stress = 0.0
                    components = []

                    for case_col, mult_col in self.combination_table:
                        case_id = rs_row[case_col]
                        multiplier = rs_row[mult_col]
                        if pd.isna(case_id) or pd.isna(multiplier):
                            continue
                        case_id = int(case_id)
                        multiplier = float(multiplier)

                        key = (case_id, int(eid))
                        if key in lookup:
                            stress = lookup[key]
                            if stress is not None:
                                total_stress += stress * multiplier
                                components.append(f"{case_id}*{multiplier}")

                    if components:
                        pid = self.elem_to_prop.get(int(eid))
                        struct_name = self.bar_structure_map.get(pid, '') if pid else ''
                        results.append({
                            'Combined_LC': comb_lc, 'Element': int(eid),
                            'Property': pid, 'Structure': struct_name,
                            'Combined_Stress': total_stress,
                            'Components': ' + '.join(components)
                        })

            if results:
                comb_csv = os.path.join(folder, 'combined_stress_results.csv')
                with open(comb_csv, 'w', newline='') as f:
                    w = csv.DictWriter(f, fieldnames=['Combined_LC', 'Element', 'Property', 'Structure', 'Combined_Stress', 'Components'])
                    w.writeheader()
                    w.writerows(results)
                self.log(f"    Combined stress CSV saved ({len(results)} rows)")
                return results

        except Exception as e:
            self.log(f"    Combine error: {e}")

        return None

    # ==================== SINGLE THICKNESS ITERATION ====================
    def _run_single_iteration(self, folder):
        """Run Nastran for current thicknesses and extract stresses."""
        try:
            n_bdfs = len(self.bdf_models) if self.bdf_models else 1
            all_stresses = []

            for bdf_idx, bdf_info in enumerate(self.bdf_models):
                bdf_name = bdf_info['name']
                bdf_subfolder = os.path.join(folder, f"bdf_{bdf_idx + 1}_{os.path.splitext(bdf_name)[0]}") if n_bdfs > 1 else folder
                os.makedirs(bdf_subfolder, exist_ok=True)

                if n_bdfs > 1:
                    self.log(f"    --- BDF {bdf_idx + 1}/{n_bdfs}: {bdf_name} ---")

                # 1. Write BDF
                bdf_path = self._write_bdf_for_model(bdf_subfolder, bdf_info['model'], bdf_info['path'])

                # 2. Apply offsets
                offset_bdf = self._apply_offsets(bdf_path, bdf_subfolder)

                # 3. Run Nastran
                self.log("    Running Nastran...")
                self._run_nastran(offset_bdf or bdf_path, bdf_subfolder)

                # 4. Extract stresses
                stresses = self._extract_stresses(bdf_subfolder)
                all_stresses.extend(stresses)

                if stresses:
                    bar_s = [s for s in stresses if s['type'] == 'bar']
                    shell_s = [s for s in stresses if s['type'] == 'shell']
                    self.log(f"    Extracted: {len(bar_s)} bar, {len(shell_s)} shell stresses")

            stresses = all_stresses

            # Combine stresses using Residual Strength
            combined_stresses = None
            if self.residual_strength_df is not None:
                self.log("    Combining stresses...")
                combined_stresses = self._combine_stresses_multi(folder, n_bdfs)
                if combined_stresses:
                    self.log(f"    Combined: {len(combined_stresses)} stress combinations")

            return stresses, combined_stresses

        except Exception as e:
            self.log(f"  Iteration ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())
            return [], None

    # ==================== MAIN SWEEP LOGIC ====================
    def start_sweep(self):
        if not self.bdf_model:
            messagebox.showerror("Error", "Load BDF first")
            return
        if not self.structure_groups:
            messagebox.showerror("Error", "Load Property Excel with structure groups first")
            return

        self.is_running = True
        self.btn_start.config(state=tk.DISABLED)
        self.btn_stop.config(state=tk.NORMAL)
        self.sweep_results = {}

        threading.Thread(target=self._run_sweep, daemon=True).start()

    def stop_sweep(self):
        self.is_running = False
        self.log("\n*** STOPPING ***")

    def _run_sweep(self):
        """Main sweep: for each structure group, iterate through thicknesses."""
        try:
            bar_min = float(self.bar_min_thickness.get())
            bar_max = float(self.bar_max_thickness.get())
            step = float(self.thickness_step.get())
            output_base = self.output_folder.get()
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
            run_folder = os.path.join(output_base, f"BarSweep_{ts}")
            os.makedirs(run_folder, exist_ok=True)

            # Build thickness list
            thicknesses = []
            t = bar_min
            while t <= bar_max + 1e-9:
                thicknesses.append(round(t, 4))
                t += step

            total_groups = len(self.structure_groups)
            total_steps = total_groups * len(thicknesses)
            current_step = 0

            self.log("\n" + "=" * 70)
            self.log("BAR PROPERTY SWEEP")
            self.log("=" * 70)
            self.log(f"  Structure groups: {total_groups}")
            self.log(f"  Thickness range: {bar_min} to {bar_max} mm, step {step}")
            self.log(f"  Thickness values: {thicknesses}")
            self.log(f"  Total iterations: {total_steps}")
            self.log(f"  Output: {run_folder}")

            for group_idx, (struct_name, pids) in enumerate(sorted(self.structure_groups.items())):
                if not self.is_running:
                    break

                self.log(f"\n{'=' * 70}")
                self.log(f"STRUCTURE GROUP: {struct_name} ({group_idx + 1}/{total_groups})")
                self.log(f"  Properties: {len(pids)} -> {sorted(pids)[:20]}{'...' if len(pids) > 20 else ''}")
                self.log(f"  Only {struct_name} thicknesses will change. All other groups keep original BDF values.")
                self.log(f"{'=' * 70}")

                # Create folder for this structure
                group_folder = os.path.join(run_folder, struct_name)
                os.makedirs(group_folder, exist_ok=True)

                group_results = []

                for t_idx, thickness in enumerate(thicknesses):
                    if not self.is_running:
                        break

                    current_step += 1
                    progress = (current_step / total_steps) * 100
                    self.root.after(0, lambda p=progress: self.progress_var.set(p))

                    self.log(f"\n  --- {struct_name}: t = {thickness:.2f} mm ({t_idx + 1}/{len(thicknesses)}) ---")

                    # Set thickness for this group only
                    for pid in pids:
                        self.current_bar_thicknesses[pid] = thickness

                    # Create iteration folder
                    iter_folder = os.path.join(group_folder, f"t_{thickness:.2f}")
                    os.makedirs(iter_folder, exist_ok=True)

                    # Run iteration
                    stresses, combined_stresses = self._run_single_iteration(iter_folder)

                    # Collect stress results for this group's properties
                    group_stress_data = self._collect_group_stresses(
                        pids, stresses, combined_stresses
                    )

                    result_entry = {
                        'thickness': thickness,
                        'stresses': group_stress_data,
                        'raw_stress_count': len(stresses),
                        'combined_count': len(combined_stresses) if combined_stresses else 0,
                    }
                    group_results.append(result_entry)

                    # Log summary for this thickness
                    if group_stress_data:
                        max_stress = max(s['stress'] for s in group_stress_data) if group_stress_data else 0
                        avg_stress = np.mean([s['stress'] for s in group_stress_data]) if group_stress_data else 0
                        self.log(f"    Max stress: {max_stress:.2f}, Avg stress: {avg_stress:.2f}")
                        self.log(f"    Elements in group: {len(group_stress_data)}")

                self.sweep_results[struct_name] = group_results

                # Save group summary
                self._save_group_summary(group_folder, struct_name, group_results, pids)

                # Reset thicknesses for this group back to original BDF values
                for pid in pids:
                    self.current_bar_thicknesses[pid] = self.original_bar_thicknesses.get(pid, bar_min)

            # Save overall summary
            if self.is_running:
                self._save_overall_summary(run_folder)

            self.log(f"\n{'=' * 70}")
            self.log("SWEEP COMPLETE")
            self.log(f"  Output folder: {run_folder}")
            self.log(f"{'=' * 70}")

        except Exception as e:
            self.log(f"\nSWEEP ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())

        finally:
            self.is_running = False
            self.root.after(0, lambda: self.btn_start.config(state=tk.NORMAL))
            self.root.after(0, lambda: self.btn_stop.config(state=tk.DISABLED))
            self.root.after(0, lambda: self.progress_var.set(100))

    # ==================== STRESS COLLECTION PER GROUP ====================
    def _collect_group_stresses(self, group_pids, stresses, combined_stresses):
        """Collect stress values for elements belonging to the given property group."""
        group_pid_set = set(group_pids)
        result = []

        # Build combined stress lookup (max positive stress per element)
        combined_lookup = {}
        if combined_stresses:
            for cs in combined_stresses:
                eid = cs['Element']
                pid = self.elem_to_prop.get(eid)
                if pid and pid in group_pid_set:
                    comb_stress = cs['Combined_Stress']
                    if eid not in combined_lookup or comb_stress > combined_lookup[eid]:
                        combined_lookup[eid] = comb_stress

        # Prefer combined stress; fall back to raw stress
        seen_elements = set()
        for s in stresses:
            eid = s['eid']
            pid = self.elem_to_prop.get(eid)
            if pid not in group_pid_set:
                continue
            if eid in seen_elements:
                continue
            seen_elements.add(eid)

            if eid in combined_lookup:
                stress_val = combined_lookup[eid]
                source = 'combined'
            else:
                stress_val = s['stress']
                source = 'raw'

            result.append({
                'eid': eid,
                'pid': pid,
                'stress': stress_val,
                'source': source,
            })

        return result

    # ==================== SUMMARY GENERATION ====================
    def _save_group_summary(self, group_folder, struct_name, group_results, pids):
        """Save a CSV summary: thickness vs stress for this structure group."""
        try:
            # Per-property summary: each row = thickness, columns = per-PID max stress
            summary_rows = []
            all_pids_in_results = set()

            for gr in group_results:
                for s in gr['stresses']:
                    all_pids_in_results.add(s['pid'])

            sorted_pids = sorted(all_pids_in_results)

            for gr in group_results:
                row = {'Thickness_mm': gr['thickness']}

                # Per-PID max positive stress
                pid_stresses = {}
                for s in gr['stresses']:
                    pid = s['pid']
                    stress_val = s['stress']
                    if pid not in pid_stresses or stress_val > pid_stresses[pid]:
                        pid_stresses[pid] = stress_val

                for pid in sorted_pids:
                    row[f'PID_{pid}_Stress'] = pid_stresses.get(pid, '')

                # Aggregates (max positive)
                all_stress_vals = [s['stress'] for s in gr['stresses']] if gr['stresses'] else []
                row['Max_Stress'] = max(all_stress_vals) if all_stress_vals else ''
                row['Avg_Stress'] = np.mean(all_stress_vals) if all_stress_vals else ''
                row['Min_Stress'] = min(all_stress_vals) if all_stress_vals else ''
                row['Element_Count'] = len(gr['stresses'])

                summary_rows.append(row)

            if summary_rows:
                # Build column order
                columns = ['Thickness_mm']
                columns += [f'PID_{pid}_Stress' for pid in sorted_pids]
                columns += ['Max_Stress', 'Avg_Stress', 'Min_Stress', 'Element_Count']

                df = pd.DataFrame(summary_rows, columns=columns)
                csv_path = os.path.join(group_folder, f"{struct_name}_summary.csv")
                df.to_csv(csv_path, index=False)
                self.log(f"\n  Summary saved: {csv_path}")

                # Also save element-level detail (max positive stress, not abs)
                detail_rows = []
                for gr in group_results:
                    for s in gr['stresses']:
                        detail_rows.append({
                            'Thickness_mm': gr['thickness'],
                            'Element_ID': s['eid'],
                            'Property_ID': s['pid'],
                            'Stress': s['stress'],
                            'Source': s['source'],
                        })

                if detail_rows:
                    detail_df = pd.DataFrame(detail_rows)
                    detail_csv = os.path.join(group_folder, f"{struct_name}_detail.csv")
                    detail_df.to_csv(detail_csv, index=False)
                    self.log(f"  Detail saved: {detail_csv}")

                # Power law fit per element: stress = a * thickness^b
                self._save_powerlaw_fit(group_folder, struct_name, group_results)

                # Element-based load/strain driven summary
                self._save_load_strain_summary(group_folder, struct_name, group_results)

        except Exception as e:
            self.log(f"  Summary save error: {e}")

    def _save_powerlaw_fit(self, group_folder, struct_name, group_results):
        """Fit power law (stress = a * thickness^b) per element and save summary."""
        try:
            # Build per-element data: eid -> [(thickness, stress), ...]
            elem_data = {}
            elem_pid = {}
            for gr in group_results:
                t = gr['thickness']
                for s in gr['stresses']:
                    eid = s['eid']
                    if eid not in elem_data:
                        elem_data[eid] = []
                        elem_pid[eid] = s['pid']
                    elem_data[eid].append((t, s['stress']))

            if not elem_data:
                return

            def power_law(x, a, b):
                return a * np.power(x, b)

            fit_rows = []
            for eid in sorted(elem_data.keys()):
                points = elem_data[eid]
                pid = elem_pid[eid]

                t_arr = np.array([p[0] for p in points])
                s_arr = np.array([p[1] for p in points])

                # Need at least 2 positive points for power law fit
                valid = (t_arr > 0) & (s_arr > 0)
                t_valid = t_arr[valid]
                s_valid = s_arr[valid]

                if len(t_valid) < 2:
                    fit_rows.append({
                        'Element_ID': eid,
                        'Property_ID': pid,
                        'Structure': struct_name,
                        'a': '',
                        'b': '',
                        'R2': '',
                        'N_Points': len(t_valid),
                        'Status': 'insufficient_data',
                    })
                    continue

                try:
                    # Log-space linear regression for power law: log(s) = log(a) + b*log(t)
                    log_t = np.log(t_valid)
                    log_s = np.log(s_valid)
                    coeffs = np.polyfit(log_t, log_s, 1)
                    b_val = coeffs[0]
                    a_val = np.exp(coeffs[1])

                    # R^2 calculation
                    s_pred = a_val * np.power(t_valid, b_val)
                    ss_res = np.sum((s_valid - s_pred) ** 2)
                    ss_tot = np.sum((s_valid - np.mean(s_valid)) ** 2)
                    r2 = 1.0 - (ss_res / ss_tot) if ss_tot > 0 else 0.0

                    fit_rows.append({
                        'Element_ID': eid,
                        'Property_ID': pid,
                        'Structure': struct_name,
                        'a': round(a_val, 4),
                        'b': round(b_val, 4),
                        'R2': round(r2, 6),
                        'N_Points': len(t_valid),
                        'Status': 'ok',
                    })
                except Exception:
                    fit_rows.append({
                        'Element_ID': eid,
                        'Property_ID': pid,
                        'Structure': struct_name,
                        'a': '',
                        'b': '',
                        'R2': '',
                        'N_Points': len(t_valid),
                        'Status': 'fit_failed',
                    })

            if fit_rows:
                fit_df = pd.DataFrame(fit_rows)
                fit_csv = os.path.join(group_folder, f"{struct_name}_powerlaw_fit.csv")
                fit_df.to_csv(fit_csv, index=False)
                self.log(f"  Power law fit saved: {fit_csv}")

                # Log summary stats
                ok_fits = [r for r in fit_rows if r['Status'] == 'ok']
                if ok_fits:
                    r2_vals = [r['R2'] for r in ok_fits]
                    self.log(f"    Fitted {len(ok_fits)}/{len(fit_rows)} elements")
                    self.log(f"    R2 range: {min(r2_vals):.4f} - {max(r2_vals):.4f}")
                    self.log(f"    R2 mean:  {np.mean(r2_vals):.4f}")

        except Exception as e:
            self.log(f"  Power law fit error: {e}")

    def _save_load_strain_summary(self, group_folder, struct_name, group_results):
        """Element-based load/strain driven summary.
        Compares stress at min vs max thickness for each element.
        If stress drops significantly with thickness increase -> LOAD driven (stress ~ 1/A)
        If stress stays similar despite thickness increase -> STRAIN driven (stress ~ geometry)
        """
        try:
            if len(group_results) < 2:
                return

            t_min = group_results[0]['thickness']
            t_max = group_results[-1]['thickness']

            # Build stress at min and max thickness per element
            stress_at_min = {}  # eid -> stress
            stress_at_max = {}  # eid -> stress
            elem_pid_map = {}

            for s in group_results[0]['stresses']:
                stress_at_min[s['eid']] = s['stress']
                elem_pid_map[s['eid']] = s['pid']

            for s in group_results[-1]['stresses']:
                stress_at_max[s['eid']] = s['stress']
                if s['eid'] not in elem_pid_map:
                    elem_pid_map[s['eid']] = s['pid']

            # Also get power law fit data for each element
            elem_fit = {}
            elem_data = {}
            for gr in group_results:
                t = gr['thickness']
                for s in gr['stresses']:
                    eid = s['eid']
                    if eid not in elem_data:
                        elem_data[eid] = []
                    elem_data[eid].append((t, s['stress']))

            for eid, points in elem_data.items():
                t_arr = np.array([p[0] for p in points])
                s_arr = np.array([p[1] for p in points])
                valid = (t_arr > 0) & (s_arr > 0)
                t_v = t_arr[valid]
                s_v = s_arr[valid]
                if len(t_v) >= 2:
                    try:
                        log_t = np.log(t_v)
                        log_s = np.log(s_v)
                        coeffs = np.polyfit(log_t, log_s, 1)
                        b_val = coeffs[0]
                        a_val = np.exp(coeffs[1])
                        s_pred = a_val * np.power(t_v, b_val)
                        ss_res = np.sum((s_v - s_pred) ** 2)
                        ss_tot = np.sum((s_v - np.mean(s_v)) ** 2)
                        r2 = 1.0 - (ss_res / ss_tot) if ss_tot > 0 else 0.0
                        elem_fit[eid] = {'a': a_val, 'b': b_val, 'r2': r2}
                    except:
                        pass

            all_eids = sorted(set(stress_at_min.keys()) | set(stress_at_max.keys()))

            rows = []
            for eid in all_eids:
                pid = elem_pid_map.get(eid, '')
                s_min_t = stress_at_min.get(eid)
                s_max_t = stress_at_max.get(eid)

                if s_min_t is None or s_max_t is None:
                    continue

                stress_diff = s_min_t - s_max_t
                stress_pct = (stress_diff / s_min_t * 100) if s_min_t != 0 else 0
                thickness_ratio = t_max / t_min if t_min > 0 else 0

                # Classification based on power law exponent b
                # b ~ -1: pure load driven (stress = F/A, inversely proportional)
                # b ~ 0: strain driven (stress doesn't change much with thickness)
                fit = elem_fit.get(eid)
                if fit:
                    b_val = fit['b']
                    a_val = fit['a']
                    r2 = fit['r2']
                    if b_val <= -0.5:
                        classification = 'LOAD_DRIVEN'
                    elif b_val <= -0.1:
                        classification = 'PARTIALLY_LOAD'
                    elif b_val <= 0.1:
                        classification = 'STRAIN_DRIVEN'
                    else:
                        classification = 'INCREASING'
                else:
                    a_val = ''
                    b_val = ''
                    r2 = ''
                    classification = 'NO_FIT'

                rows.append({
                    'Element_ID': eid,
                    'Property_ID': pid,
                    'Structure': struct_name,
                    'T_Min_mm': t_min,
                    'Stress_at_T_Min': round(s_min_t, 4),
                    'T_Max_mm': t_max,
                    'Stress_at_T_Max': round(s_max_t, 4),
                    'Stress_Drop': round(stress_diff, 4),
                    'Stress_Drop_Pct': round(stress_pct, 2),
                    'Thickness_Ratio': round(thickness_ratio, 4),
                    'Power_a': round(a_val, 4) if isinstance(a_val, float) else '',
                    'Power_b': round(b_val, 4) if isinstance(b_val, float) else '',
                    'R2': round(r2, 6) if isinstance(r2, float) else '',
                    'Classification': classification,
                })

            if rows:
                df = pd.DataFrame(rows)
                csv_path = os.path.join(group_folder, f"{struct_name}_load_strain_summary.csv")
                df.to_csv(csv_path, index=False)
                self.log(f"  Load/Strain summary saved: {csv_path}")

                # Log classification counts
                cls_counts = {}
                for r in rows:
                    c = r['Classification']
                    cls_counts[c] = cls_counts.get(c, 0) + 1
                for c, cnt in sorted(cls_counts.items()):
                    self.log(f"    {c}: {cnt} elements")

        except Exception as e:
            self.log(f"  Load/Strain summary error: {e}")

    def _save_overall_summary(self, run_folder):
        """Save overall summary across all structure groups."""
        try:
            self.log("\n" + "-" * 70)
            self.log("OVERALL SUMMARY")
            self.log("-" * 70)

            overall_rows = []
            for struct_name, results in sorted(self.sweep_results.items()):
                for gr in results:
                    all_stress_vals = [s['stress'] for s in gr['stresses']] if gr['stresses'] else []
                    overall_rows.append({
                        'Structure': struct_name,
                        'Thickness_mm': gr['thickness'],
                        'Max_Stress': max(all_stress_vals) if all_stress_vals else '',
                        'Avg_Stress': np.mean(all_stress_vals) if all_stress_vals else '',
                        'Min_Stress': min(all_stress_vals) if all_stress_vals else '',
                        'Element_Count': len(gr['stresses']),
                    })

                    if all_stress_vals:
                        self.log(f"  {struct_name} | t={gr['thickness']:.2f}mm | "
                                 f"Max={max(all_stress_vals):.2f} | Avg={np.mean(all_stress_vals):.2f}")

            if overall_rows:
                df = pd.DataFrame(overall_rows)
                csv_path = os.path.join(run_folder, "overall_summary.csv")
                df.to_csv(csv_path, index=False)
                self.log(f"\n  Overall summary saved: {csv_path}")

            # Save run config
            config_path = os.path.join(run_folder, "run_config.txt")
            with open(config_path, 'w') as f:
                f.write(f"Bar Property Solver v1.0\n")
                f.write(f"Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
                f.write(f"Bar Min: {self.bar_min_thickness.get()} mm\n")
                f.write(f"Bar Max: {self.bar_max_thickness.get()} mm\n")
                f.write(f"Step: {self.thickness_step.get()} mm\n")
                f.write(f"BDF Files: {len(self.bdf_paths)}\n")
                for p in self.bdf_paths:
                    f.write(f"  {p}\n")
                f.write(f"Structure Groups: {len(self.structure_groups)}\n")
                for name, pids in sorted(self.structure_groups.items()):
                    f.write(f"  {name}: {len(pids)} properties\n")

        except Exception as e:
            self.log(f"  Overall summary error: {e}")

    # ==================== EXPORT ====================
    def export_results(self):
        if not self.sweep_results:
            messagebox.showerror("Error", "No results to export. Run sweep first.")
            return

        try:
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
            path = os.path.join(self.output_folder.get(), f"bar_sweep_results_{ts}.xlsx")

            with pd.ExcelWriter(path, engine='openpyxl') as writer:
                # Overall sheet
                overall_rows = []
                for struct_name, results in sorted(self.sweep_results.items()):
                    for gr in results:
                        all_s = [abs(s['stress']) for s in gr['stresses']] if gr['stresses'] else []
                        overall_rows.append({
                            'Structure': struct_name,
                            'Thickness_mm': gr['thickness'],
                            'Max_Stress': max(all_s) if all_s else None,
                            'Avg_Stress': np.mean(all_s) if all_s else None,
                            'Min_Stress': min(all_s) if all_s else None,
                            'Element_Count': len(gr['stresses']),
                        })
                if overall_rows:
                    pd.DataFrame(overall_rows).to_excel(writer, sheet_name='Overall', index=False)

                # Per-group sheets
                for struct_name, results in sorted(self.sweep_results.items()):
                    sheet_name = struct_name[:31]  # Excel 31 char limit
                    detail_rows = []
                    for gr in results:
                        for s in gr['stresses']:
                            detail_rows.append({
                                'Thickness_mm': gr['thickness'],
                                'Element_ID': s['eid'],
                                'Property_ID': s['pid'],
                                'Stress': s['stress'],
                                'Abs_Stress': abs(s['stress']),
                                'Source': s['source'],
                            })
                    if detail_rows:
                        pd.DataFrame(detail_rows).to_excel(writer, sheet_name=sheet_name, index=False)

            self.log(f"\nExported: {path}")
            messagebox.showinfo("Export", f"Saved to:\n{path}")

        except Exception as e:
            self.log(f"Export error: {e}")
            messagebox.showerror("Error", str(e))


def main():
    root = tk.Tk()
    app = BarPropertySolver(root)
    root.mainloop()


if __name__ == "__main__":
    main()
