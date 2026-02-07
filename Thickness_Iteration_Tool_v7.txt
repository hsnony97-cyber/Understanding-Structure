#!/usr/bin/env python3
"""
Thickness Iteration Tool v3.0
==============================
Per-property thickness optimization with RF Check v2.1 allowable fitting logic.

Features:
- RF Check v2.1 compatible allowable reading (exact same logic)
- Per-property individual thickness optimization
- MAT1/MAT8/MAT9 density support
- THREE optimization algorithms:
  1. Simple Iterative
  2. Fast GA (Surrogate Model)
  3. Hybrid GA + Nastran
- Minimum weight objective with RF constraint
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
import random
import copy
from scipy.optimize import minimize
from itertools import combinations


class ThicknessIterationTool:
    def __init__(self, root):
        self.root = root
        self.root.title("Thickness Iteration Tool v3.0")
        self.root.geometry("1300x1000")

        # Input paths
        self.input_bdf_path = tk.StringVar()
        self.bdf_paths = []  # List of BDF paths for multi-BDF support
        self.allowable_excel_path = tk.StringVar()
        self.property_excel_path = tk.StringVar()
        self.element_excel_path = tk.StringVar()
        self.residual_strength_path = tk.StringVar()  # NEW: Residual Strength Excel
        self.nastran_path = tk.StringVar()
        self.output_folder = tk.StringVar()

        # Thickness ranges
        self.bar_min_thickness = tk.StringVar(value="2.0")
        self.bar_max_thickness = tk.StringVar(value="12.0")
        self.skin_min_thickness = tk.StringVar(value="3.0")
        self.skin_max_thickness = tk.StringVar(value="18.0")
        self.thickness_step = tk.StringVar(value="0.5")
        self.bar_skin_search_distance = tk.StringVar(value="150.0")  # mm - for proximity-based optimization

        # RF settings
        self.target_rf = tk.StringVar(value="1.0")
        self.rf_tolerance = tk.StringVar(value="0.05")
        self.r2_threshold_var = tk.StringVar(value="0.95")
        self.min_data_points_var = tk.StringVar(value="3")

        # Optimization settings
        self.max_iterations = tk.StringVar(value="50")
        self.algorithm_var = tk.StringVar(value="Simple Iterative")

        # GA Parameters
        self.ga_population = tk.StringVar(value="50")
        self.ga_generations = tk.StringVar(value="100")
        self.ga_mutation_rate = tk.StringVar(value="0.1")
        self.ga_crossover_rate = tk.StringVar(value="0.8")

        # Data storage
        self.bdf_model = None
        self.bar_properties = {}
        self.skin_properties = {}
        self.pbarl_dims = {}  # PID -> {'dim1': val, 'dim2': val} from BDF PBARL

        # Per-property current thicknesses
        self.current_bar_thicknesses = {}  # PID -> thickness
        self.current_skin_thicknesses = {}  # PID -> thickness

        # Material densities from BDF (MAT1, MAT8, MAT9, etc.)
        self.material_densities = {}  # MID -> density
        self.prop_to_material = {}  # PID -> MID

        # Geometry
        self.element_areas = {}
        self.bar_lengths = {}
        self.prop_elements = {}
        self.elem_to_prop = {}
        self.element_centroids = {}  # EID -> (x, y, z) centroid coordinates
        self.bar_to_nearby_skins = {}  # Bar PID -> list of nearby Skin PIDs

        # Allowable fits (RF Check v2.1 format)
        self.allowable_interp = {}  # PID -> {a, b, r2, excluded, n_pts}
        self.allowable_elem_interp = {}  # EID -> {a, b, r2, excluded, property}
        self.allowable_df = None

        # Residual Strength data for stress combination
        self.residual_strength_df = None
        self.combination_table = []  # [(case_col, mult_col), ...]

        # Reference stresses for surrogate model
        self.reference_stresses = {}  # PID -> stress at reference thickness
        self.reference_thickness = {}  # PID -> reference thickness

        # Offset elements
        self.landing_elem_ids = []
        self.bar_offset_elem_ids = []

        # Results
        self.iteration_results = []
        self.best_solution = None
        self.is_running = False

        self.setup_ui()

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

        ttk.Label(main, text="Thickness Iteration Tool v2.1", font=('Helvetica', 16, 'bold')).pack(pady=10)
        ttk.Label(main, text="Per-property optimization with RF Check v2.1 allowable logic", foreground='gray').pack()

        # Section 1: Input Files
        f1 = ttk.LabelFrame(main, text="1. Input Files", padding=10)
        f1.pack(fill=tk.X, pady=5, padx=10)

        # Multi-BDF selection with Listbox
        bdf_frame = ttk.Frame(f1)
        bdf_frame.pack(fill=tk.X, pady=2)
        ttk.Label(bdf_frame, text="BDF Files:", width=18).pack(side=tk.LEFT, anchor=tk.N)

        bdf_list_frame = ttk.Frame(bdf_frame)
        bdf_list_frame.pack(side=tk.LEFT, fill=tk.X, expand=True)

        self.bdf_listbox = tk.Listbox(bdf_list_frame, height=3, width=55, selectmode=tk.SINGLE)
        self.bdf_listbox.pack(side=tk.LEFT, fill=tk.X, expand=True)

        bdf_scroll = ttk.Scrollbar(bdf_list_frame, orient=tk.VERTICAL, command=self.bdf_listbox.yview)
        bdf_scroll.pack(side=tk.LEFT, fill=tk.Y)
        self.bdf_listbox.config(yscrollcommand=bdf_scroll.set)

        bdf_btn_frame = ttk.Frame(bdf_frame)
        bdf_btn_frame.pack(side=tk.LEFT, padx=5)
        ttk.Button(bdf_btn_frame, text="Add", command=self.add_bdf, width=8).pack(pady=1)
        ttk.Button(bdf_btn_frame, text="Remove", command=self.remove_bdf, width=8).pack(pady=1)
        ttk.Button(bdf_btn_frame, text="Load All", command=self.load_bdf, width=8).pack(pady=1)

        self.bdf_status = ttk.Label(f1, text="No BDF files loaded", foreground="gray")
        self.bdf_status.pack(anchor=tk.W)

        for label, var, cmd, status_name in [
            ("Property Excel:", self.property_excel_path, self.load_properties, "prop_status"),
            ("Allowable Excel:", self.allowable_excel_path, self.rf_load_allowable, "allow_status"),
            ("Residual Strength:", self.residual_strength_path, self.load_residual_strength, "resid_status"),
            ("Offset Element IDs:", self.element_excel_path, self.load_element_ids, "elem_status"),
        ]:
            row = ttk.Frame(f1)
            row.pack(fill=tk.X, pady=2)
            ttk.Label(row, text=label, width=18).pack(side=tk.LEFT)
            ttk.Entry(row, textvariable=var, width=50).pack(side=tk.LEFT, padx=5)
            ttk.Button(row, text="Browse", command=lambda v=var: self.browse_file(v)).pack(side=tk.LEFT)
            ttk.Button(row, text="Load", command=cmd).pack(side=tk.LEFT, padx=2)
            setattr(self, status_name, ttk.Label(f1, text="Not loaded", foreground="gray"))
            getattr(self, status_name).pack(anchor=tk.W)

        row = ttk.Frame(f1)
        row.pack(fill=tk.X, pady=2)
        ttk.Label(row, text="Nastran Exe:", width=18).pack(side=tk.LEFT)
        ttk.Entry(row, textvariable=self.nastran_path, width=50).pack(side=tk.LEFT, padx=5)
        ttk.Button(row, text="Browse", command=lambda: self.browse_file(self.nastran_path)).pack(side=tk.LEFT)

        row = ttk.Frame(f1)
        row.pack(fill=tk.X, pady=2)
        ttk.Label(row, text="Output Folder:", width=18).pack(side=tk.LEFT)
        ttk.Entry(row, textvariable=self.output_folder, width=50).pack(side=tk.LEFT, padx=5)
        ttk.Button(row, text="Browse", command=self.browse_folder).pack(side=tk.LEFT)

        # Section 2: Thickness Ranges
        f2 = ttk.LabelFrame(main, text="2. Thickness Ranges (mm)", padding=10)
        f2.pack(fill=tk.X, pady=5, padx=10)

        row = ttk.Frame(f2)
        row.pack(fill=tk.X, pady=3)
        ttk.Label(row, text="Bar:").pack(side=tk.LEFT)
        ttk.Label(row, text="Min:").pack(side=tk.LEFT, padx=5)
        ttk.Entry(row, textvariable=self.bar_min_thickness, width=8).pack(side=tk.LEFT)
        ttk.Label(row, text="Max:").pack(side=tk.LEFT, padx=5)
        ttk.Entry(row, textvariable=self.bar_max_thickness, width=8).pack(side=tk.LEFT)

        row = ttk.Frame(f2)
        row.pack(fill=tk.X, pady=3)
        ttk.Label(row, text="Skin:").pack(side=tk.LEFT)
        ttk.Label(row, text="Min:").pack(side=tk.LEFT, padx=5)
        ttk.Entry(row, textvariable=self.skin_min_thickness, width=8).pack(side=tk.LEFT)
        ttk.Label(row, text="Max:").pack(side=tk.LEFT, padx=5)
        ttk.Entry(row, textvariable=self.skin_max_thickness, width=8).pack(side=tk.LEFT)

        row = ttk.Frame(f2)
        row.pack(fill=tk.X, pady=3)
        ttk.Label(row, text="Step:").pack(side=tk.LEFT)
        ttk.Entry(row, textvariable=self.thickness_step, width=8).pack(side=tk.LEFT, padx=5)
        ttk.Label(row, text="Bar-Skin Distance (mm):").pack(side=tk.LEFT, padx=10)
        ttk.Entry(row, textvariable=self.bar_skin_search_distance, width=8).pack(side=tk.LEFT)

        # Section 3: RF Settings
        f3 = ttk.LabelFrame(main, text="3. RF Settings", padding=10)
        f3.pack(fill=tk.X, pady=5, padx=10)

        row = ttk.Frame(f3)
        row.pack(fill=tk.X, pady=3)
        ttk.Label(row, text="Target RF:").pack(side=tk.LEFT)
        ttk.Entry(row, textvariable=self.target_rf, width=8).pack(side=tk.LEFT, padx=5)
        ttk.Label(row, text="Tolerance:").pack(side=tk.LEFT, padx=10)
        ttk.Entry(row, textvariable=self.rf_tolerance, width=8).pack(side=tk.LEFT)

        row = ttk.Frame(f3)
        row.pack(fill=tk.X, pady=3)
        ttk.Label(row, text="R² Threshold:").pack(side=tk.LEFT)
        ttk.Entry(row, textvariable=self.r2_threshold_var, width=8).pack(side=tk.LEFT, padx=5)
        ttk.Label(row, text="Min Points:").pack(side=tk.LEFT, padx=10)
        ttk.Entry(row, textvariable=self.min_data_points_var, width=8).pack(side=tk.LEFT)

        # Section 4: Optimization Algorithm
        f4 = ttk.LabelFrame(main, text="4. Optimization Algorithm", padding=10)
        f4.pack(fill=tk.X, pady=5, padx=10)

        row = ttk.Frame(f4)
        row.pack(fill=tk.X, pady=3)
        ttk.Label(row, text="Algorithm:").pack(side=tk.LEFT)
        algo_combo = ttk.Combobox(row, textvariable=self.algorithm_var, width=25, state='readonly')
        algo_combo['values'] = ('Simple Iterative', 'Fast GA (Surrogate)', 'Full GA + Nastran', 'Surrogate-Assisted GA', 'RSM + SQP', 'Hybrid GA + Nastran', 'Top-Down (Max to Target)', 'Bottom-Up (Min to Target)')
        algo_combo.pack(side=tk.LEFT, padx=5)
        algo_combo.bind('<<ComboboxSelected>>', self._on_algorithm_change)

        ttk.Label(row, text="Max Iterations:").pack(side=tk.LEFT, padx=10)
        ttk.Entry(row, textvariable=self.max_iterations, width=8).pack(side=tk.LEFT, padx=5)

        # GA Parameters Frame
        self.ga_frame = ttk.LabelFrame(f4, text="GA Parameters", padding=5)
        self.ga_frame.pack(fill=tk.X, pady=5)

        row = ttk.Frame(self.ga_frame)
        row.pack(fill=tk.X, pady=2)
        ttk.Label(row, text="Population:").pack(side=tk.LEFT)
        ttk.Entry(row, textvariable=self.ga_population, width=8).pack(side=tk.LEFT, padx=5)
        ttk.Label(row, text="Generations:").pack(side=tk.LEFT, padx=10)
        ttk.Entry(row, textvariable=self.ga_generations, width=8).pack(side=tk.LEFT, padx=5)

        row = ttk.Frame(self.ga_frame)
        row.pack(fill=tk.X, pady=2)
        ttk.Label(row, text="Mutation Rate:").pack(side=tk.LEFT)
        ttk.Entry(row, textvariable=self.ga_mutation_rate, width=8).pack(side=tk.LEFT, padx=5)
        ttk.Label(row, text="Crossover Rate:").pack(side=tk.LEFT, padx=10)
        ttk.Entry(row, textvariable=self.ga_crossover_rate, width=8).pack(side=tk.LEFT, padx=5)

        # Initially hide GA parameters
        self.ga_frame.pack_forget()

        # Section 5: Actions
        f5 = ttk.LabelFrame(main, text="5. Actions", padding=10)
        f5.pack(fill=tk.X, pady=5, padx=10)

        row = ttk.Frame(f5)
        row.pack(fill=tk.X, pady=5)
        self.btn_start = ttk.Button(row, text=">>> START OPTIMIZATION <<<", command=self.start_optimization, width=25)
        self.btn_start.pack(side=tk.LEFT, padx=5)
        self.btn_stop = ttk.Button(row, text="STOP", command=self.stop_optimization, width=10, state=tk.DISABLED)
        self.btn_stop.pack(side=tk.LEFT, padx=5)
        ttk.Button(row, text="Clear Log", command=self.clear_log).pack(side=tk.LEFT, padx=5)
        ttk.Button(row, text="Export", command=self.export_results).pack(side=tk.LEFT, padx=5)

        self.progress = ttk.Progressbar(f5, mode='determinate')
        self.progress.pack(fill=tk.X, pady=5)
        self.progress_label = ttk.Label(f5, text="Ready")
        self.progress_label.pack(anchor=tk.W)

        # Section 6: Results
        f6 = ttk.LabelFrame(main, text="6. Results", padding=10)
        f6.pack(fill=tk.X, pady=5, padx=10)

        self.result_summary = ttk.Label(f6, text="Run optimization to see results", font=('Helvetica', 11, 'bold'), foreground='blue')
        self.result_summary.pack(anchor=tk.W, pady=5)

        self.best_text = tk.Text(f6, height=10, font=('Courier', 9))
        self.best_text.pack(fill=tk.X, pady=5)

        # Section 7: Log
        f7 = ttk.LabelFrame(main, text="7. Log", padding=10)
        f7.pack(fill=tk.BOTH, expand=True, pady=5, padx=10)

        self.log_text = scrolledtext.ScrolledText(f7, height=15, font=('Courier', 9))
        self.log_text.pack(fill=tk.BOTH, expand=True)

        self.log("="*70)
        self.log("Thickness Iteration Tool v3.0")
        self.log("Per-property optimization with 3 algorithms")
        self.log("  1. Simple Iterative")
        self.log("  2. Fast GA (Surrogate Model)")
        self.log("  3. Hybrid GA + Nastran")
        self.log("="*70)

    def _on_algorithm_change(self, event=None):
        """Show/hide GA parameters based on selected algorithm."""
        algo = self.algorithm_var.get()
        if 'GA' in algo:
            self.ga_frame.pack(fill=tk.X, pady=5)
        else:
            self.ga_frame.pack_forget()

    def log(self, msg):
        self.log_text.insert(tk.END, msg + "\n")
        self.log_text.see(tk.END)
        self.root.update_idletasks()

    def clear_log(self):
        self.log_text.delete(1.0, tk.END)

    def update_progress(self, val, txt=""):
        self.progress['value'] = val
        self.progress_label.config(text=txt)
        self.root.update_idletasks()

    def browse_file(self, var):
        f = filedialog.askopenfilename()
        if f:
            var.set(f)

    def browse_folder(self):
        f = filedialog.askdirectory()
        if f:
            self.output_folder.set(f)

    def add_bdf(self):
        """Add BDF file to the list."""
        files = filedialog.askopenfilenames(
            title="Select BDF files",
            filetypes=[("BDF files", "*.bdf *.dat *.nas"), ("All files", "*.*")]
        )
        for f in files:
            if f and f not in self.bdf_paths:
                self.bdf_paths.append(f)
                self.bdf_listbox.insert(tk.END, os.path.basename(f))
        self.bdf_status.config(text=f"{len(self.bdf_paths)} BDF files selected", foreground="blue")

    def remove_bdf(self):
        """Remove selected BDF from list."""
        selection = self.bdf_listbox.curselection()
        if selection:
            idx = selection[0]
            self.bdf_listbox.delete(idx)
            del self.bdf_paths[idx]
        self.bdf_status.config(text=f"{len(self.bdf_paths)} BDF files selected", foreground="blue")

    # ==================== BDF LOADING ====================
    def load_bdf(self):
        """Load all BDF files in the list."""
        if not self.bdf_paths:
            messagebox.showerror("Error", "Add at least one BDF file")
            return

        self.log("\n" + "="*70)
        self.log("LOADING BDF FILES")
        self.log("="*70)
        self.log(f"  BDF files to load: {len(self.bdf_paths)}")
        for i, p in enumerate(self.bdf_paths):
            self.log(f"    {i+1}. {os.path.basename(p)}")

        try:
            # Load the FIRST BDF as the main model (for geometry extraction)
            path = self.bdf_paths[0]
            self.log(f"\n  Loading main BDF: {os.path.basename(path)}")
            self.bdf_model = BDF(debug=False)
            self.bdf_model.read_bdf(path, validate=False, xref=True, read_includes=True, encoding='latin-1')

            # Store all BDF models for multi-BDF processing
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

            # Extract material densities (MAT1, MAT2, MAT8, MAT9, etc.)
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
            self.bar_elements = []  # List of bar element IDs
            self.shell_elements = []  # List of shell element IDs

            shell_count = bar_count = 0

            for eid, elem in self.bdf_model.elements.items():
                pid = elem.pid if hasattr(elem, 'pid') else None
                if pid:
                    self.elem_to_prop[eid] = pid
                    if pid not in self.prop_elements:
                        self.prop_elements[pid] = []
                    self.prop_elements[pid].append(eid)

                # Try to get centroid
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

            # Extract PBARL dimensions from BDF (for accurate Dim2 values)
            self.pbarl_dims = {}
            for pid, prop in self.bdf_model.properties.items():
                if prop.type == 'PBARL':
                    dims = prop.dim if hasattr(prop, 'dim') else []
                    if len(dims) >= 2:
                        self.pbarl_dims[pid] = {
                            'dim1': dims[0],
                            'dim2': dims[1],
                        }
                    elif len(dims) == 1:
                        self.pbarl_dims[pid] = {
                            'dim1': dims[0],
                            'dim2': dims[0],
                        }
            if self.pbarl_dims:
                self.log(f"  PBARL dimensions extracted: {len(self.pbarl_dims)} properties")
                for pid, d in self.pbarl_dims.items():
                    self.log(f"    PID {pid}: dim1={d['dim1']}, dim2={d['dim2']}")

            self.log(f"  Shells: {shell_count}, Bars: {bar_count}")
            self.log(f"  Centroids calculated: {len(self.element_centroids)}")
            self.log(f"\n  Total BDF models loaded: {len(self.bdf_models)}")

            self.bdf_status.config(text=f"✓ {len(self.bdf_models)} BDFs, {len(self.bdf_model.elements)} elements", foreground="green")

            if not self.output_folder.get():
                self.output_folder.set(os.path.dirname(path))

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())
            self.bdf_status.config(text="Error", foreground="red")

    def calculate_bar_skin_proximity(self):
        """Calculate which skin properties are near each bar property based on search distance."""
        import numpy as np

        search_dist = float(self.bar_skin_search_distance.get())
        self.log(f"\n  Calculating bar-skin proximity (distance={search_dist} mm)...")

        self.bar_to_nearby_skins = {}

        if not self.element_centroids:
            self.log("    WARNING: No element centroids available!")
            return

        # Get bar property -> bar element centroids
        bar_prop_centroids = {}  # bar_pid -> list of centroids
        for bar_eid in self.bar_elements:
            if bar_eid in self.element_centroids:
                bar_pid = self.elem_to_prop.get(bar_eid)
                if bar_pid and bar_pid in self.bar_properties:
                    if bar_pid not in bar_prop_centroids:
                        bar_prop_centroids[bar_pid] = []
                    bar_prop_centroids[bar_pid].append(self.element_centroids[bar_eid])

        # Get shell property -> shell element centroids
        shell_prop_centroids = {}  # skin_pid -> list of centroids
        for shell_eid in self.shell_elements:
            if shell_eid in self.element_centroids:
                shell_pid = self.elem_to_prop.get(shell_eid)
                if shell_pid and shell_pid in self.skin_properties:
                    if shell_pid not in shell_prop_centroids:
                        shell_prop_centroids[shell_pid] = []
                    shell_prop_centroids[shell_pid].append(self.element_centroids[shell_eid])

        # For each bar property, find nearby skin properties
        for bar_pid, bar_cents in bar_prop_centroids.items():
            nearby_skins = set()

            for skin_pid, skin_cents in shell_prop_centroids.items():
                # Check if any bar element is close to any shell element of this property
                is_nearby = False
                for bc in bar_cents:
                    for sc in skin_cents:
                        dist = np.sqrt((bc[0]-sc[0])**2 + (bc[1]-sc[1])**2 + (bc[2]-sc[2])**2)
                        if dist <= search_dist:
                            is_nearby = True
                            break
                    if is_nearby:
                        break

                if is_nearby:
                    nearby_skins.add(skin_pid)

            self.bar_to_nearby_skins[bar_pid] = nearby_skins

        # Log summary
        total_connections = sum(len(skins) for skins in self.bar_to_nearby_skins.values())
        avg_skins = total_connections / len(self.bar_to_nearby_skins) if self.bar_to_nearby_skins else 0
        self.log(f"    Bar properties: {len(self.bar_to_nearby_skins)}")
        self.log(f"    Total connections: {total_connections}")
        self.log(f"    Avg skins per bar: {avg_skins:.1f}")

    def load_properties(self):
        path = self.property_excel_path.get()
        if not path:
            messagebox.showerror("Error", "Select Property Excel")
            return

        self.log("\n" + "="*70)
        self.log("LOADING PROPERTIES")
        self.log("="*70)

        try:
            xl = pd.ExcelFile(path)
            self.log(f"Sheets: {xl.sheet_names}")

            bar_min = float(self.bar_min_thickness.get())
            skin_min = float(self.skin_min_thickness.get())

            self.bar_properties = {}
            self.skin_properties = {}
            self.current_bar_thicknesses = {}
            self.current_skin_thicknesses = {}

            for sheet in xl.sheet_names:
                sl = sheet.lower().replace('_', '').replace(' ', '')
                df = pd.read_excel(xl, sheet_name=sheet)

                if 'bar' in sl and 'prop' in sl:
                    self.log(f"\nReading bar properties from '{sheet}'...")
                    for _, row in df.iterrows():
                        pid = int(row.iloc[0]) if pd.notna(row.iloc[0]) else None
                        if pid:
                            self.bar_properties[pid] = {
                                'dim1': float(row.iloc[1]) if len(row) > 1 and pd.notna(row.iloc[1]) else bar_min,
                                'dim2': float(row.iloc[2]) if len(row) > 2 and pd.notna(row.iloc[2]) else bar_min,
                            }
                            self.current_bar_thicknesses[pid] = bar_min
                    self.log(f"  Loaded {len(self.bar_properties)} bar properties")

                elif 'skin' in sl and 'prop' in sl:
                    self.log(f"\nReading skin properties from '{sheet}'...")
                    for _, row in df.iterrows():
                        pid = int(row.iloc[0]) if pd.notna(row.iloc[0]) else None
                        if pid:
                            self.skin_properties[pid] = {
                                'thickness': float(row.iloc[1]) if len(row) > 1 and pd.notna(row.iloc[1]) else skin_min,
                            }
                            self.current_skin_thicknesses[pid] = skin_min
                    self.log(f"  Loaded {len(self.skin_properties)} skin properties")

            self.prop_status.config(text=f"✓ Bar: {len(self.bar_properties)}, Skin: {len(self.skin_properties)}", foreground="green")

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())
            self.prop_status.config(text="Error", foreground="red")

    # ==================== RF CHECK v2.1 ALLOWABLE LOADING (EXACT COPY) ====================
    def rf_load_allowable(self):
        """Load Allowable stress data and fit power law - EXACT RF Check v2.1 logic."""
        path = self.allowable_excel_path.get()
        if not path or not os.path.exists(path):
            messagebox.showerror("Error", "Select a valid Allowable file")
            return

        self.log("\n" + "="*70)
        self.log("LOADING ALLOWABLE DATA & FITTING POWER LAW")
        self.log("(RF Check v2.1 exact logic)")
        self.log("="*70)

        try:
            r2_threshold = float(self.r2_threshold_var.get())
            min_data_pts = int(self.min_data_points_var.get())
        except:
            r2_threshold = 0.95
            min_data_pts = 3

        self.log(f"R² Threshold: {r2_threshold}, Min Data Points: {min_data_pts}")

        try:
            # Load file
            if path.endswith('.csv'):
                raw_df = pd.read_csv(path)
            else:
                xl = pd.ExcelFile(path)
                bar_sheet = None
                for sheet in xl.sheet_names:
                    if 'bar' in sheet.lower() or 'allowable' in sheet.lower() or 'summary' in sheet.lower():
                        bar_sheet = sheet
                        break
                raw_df = pd.read_excel(path, sheet_name=bar_sheet if bar_sheet else 0)

            self.log(f"\nLoaded: {len(raw_df)} rows")
            self.log(f"Columns: {list(raw_df.columns)}")

            # Clean column names
            clean_cols = {}
            for col in raw_df.columns:
                clean_name = str(col).replace('\n', ' ').replace('\r', ' ').strip()
                clean_name = ' '.join(clean_name.split())
                clean_cols[col] = clean_name
            raw_df = raw_df.rename(columns=clean_cols)

            # Map column names (RF Check v2.1 EXACT mapping)
            col_map = {}
            for col in raw_df.columns:
                col_up = col.upper().replace(' ', '_').replace('BAR_', '').replace('(MM)', '').strip('_')

                if col_up in ['PROPERTY_ID', 'PROPERTY', 'PROP_ID']:
                    col_map[col] = 'Property'
                elif col_up in ['ELEMENT_ID', 'ELEMENT']:
                    col_map[col] = 'Element_ID'
                elif col_up in ['ELEMENT_TYPE', 'ELEMENT_TYP']:
                    col_map[col] = 'Element_Type'
                elif col_up in ['T', 'THICKNESS', 'T_MM']:
                    col_map[col] = 'Thickness'
                elif col_up in ['ALLOWABLE', 'ALLOW', 'ALLOWABLE_STRESS']:
                    col_map[col] = 'Allowable'

            self.log(f"\nColumn mapping:")
            for orig, mapped in col_map.items():
                self.log(f"  '{orig}' -> '{mapped}'")

            df = raw_df.rename(columns=col_map)

            # Save full df for element-based fitting
            df_full_elements = df.copy() if 'Element_ID' in df.columns else None

            # Check for NEW format with Element_Type
            if 'Element_Type' in df.columns or 'Element_ID' in df.columns:
                self.log("\nDetected format with Element_Type/Element_ID")
                df = self._process_new_allowable_format(df)

            self.allowable_df = df

            # Convert to numeric
            df['Thickness'] = pd.to_numeric(df['Thickness'], errors='coerce')
            df['Allowable'] = pd.to_numeric(df['Allowable'], errors='coerce')
            df['Property'] = pd.to_numeric(df['Property'], errors='coerce')
            df = df.dropna(subset=['Property', 'Thickness', 'Allowable'])

            properties = df['Property'].unique()
            self.log(f"\nFitting {len(properties)} properties...")

            self.allowable_interp = {}
            excluded_r2 = []
            excluded_data = []
            valid_props = []

            for pid in properties:
                pid_int = int(pid)
                prop_data = df[df['Property'] == pid]
                n_pts = len(prop_data)

                if n_pts < min_data_pts:
                    avg = prop_data['Allowable'].mean()
                    self.allowable_interp[pid_int] = {'a': avg, 'b': 0, 'n_pts': n_pts, 'r2': 0, 'excluded': True}
                    excluded_data.append((pid_int, n_pts))
                    continue

                try:
                    x = prop_data['Thickness'].values.astype(float)
                    y = prop_data['Allowable'].values.astype(float)

                    valid = (x > 0) & (y > 0)
                    x, y = x[valid], y[valid]

                    if len(x) < 2:
                        self.allowable_interp[pid_int] = {'a': np.mean(y), 'b': 0, 'n_pts': len(x), 'r2': 0, 'excluded': True}
                        excluded_data.append((pid_int, len(x)))
                        continue

                    # Power law fit
                    log_x, log_y = np.log(x), np.log(y)
                    coeffs = np.polyfit(log_x, log_y, 1)
                    b, log_a = coeffs[0], coeffs[1]
                    a = np.exp(log_a)

                    # R²
                    y_pred = a * (x ** b)
                    ss_res = np.sum((y - y_pred) ** 2)
                    ss_tot = np.sum((y - np.mean(y)) ** 2)
                    r2 = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0

                    if r2 < r2_threshold:
                        self.allowable_interp[pid_int] = {'a': np.mean(y), 'b': 0, 'n_pts': n_pts, 'r2': r2, 'excluded': True}
                        excluded_r2.append((pid_int, r2, n_pts))
                    else:
                        self.allowable_interp[pid_int] = {'a': a, 'b': b, 'n_pts': n_pts, 'r2': r2, 'excluded': False}
                        valid_props.append(pid_int)

                except Exception as e:
                    self.allowable_interp[pid_int] = {'a': 100, 'b': 0, 'n_pts': n_pts, 'r2': 0, 'excluded': True}
                    excluded_data.append((pid_int, n_pts))

            self.log(f"\n{'='*50}")
            self.log(f"Valid fits (R² >= {r2_threshold}): {len(valid_props)}")
            self.log(f"Excluded (R² < {r2_threshold}): {len(excluded_r2)}")
            self.log(f"Excluded (data < {min_data_pts}): {len(excluded_data)}")

            if valid_props:
                self.log(f"\nSample valid fits (Property):")
                for pid in valid_props[:5]:
                    p = self.allowable_interp[pid]
                    self.log(f"  Property {pid}: Allow = {p['a']:.4f} × T^({p['b']:.4f}), R²={p['r2']:.4f}")

            # ELEMENT-BASED CURVE FITTING
            self.allowable_elem_interp = {}

            if df_full_elements is not None and 'Element_ID' in df_full_elements.columns:
                self.log(f"\n{'='*50}")
                self.log("ELEMENT-BASED CURVE FITTING")
                self.log(f"{'='*50}")

                df_elem = df_full_elements.copy()
                df_elem['Thickness'] = pd.to_numeric(df_elem['Thickness'], errors='coerce')
                df_elem['Allowable'] = pd.to_numeric(df_elem['Allowable'], errors='coerce')
                df_elem['Element_ID'] = pd.to_numeric(df_elem['Element_ID'], errors='coerce')
                df_elem['Property'] = pd.to_numeric(df_elem['Property'], errors='coerce')
                df_elem = df_elem.dropna(subset=['Element_ID', 'Thickness', 'Allowable'])

                elements = df_elem['Element_ID'].unique()
                self.log(f"Fitting {len(elements)} elements...")

                valid_elems = []

                for elem_id in elements:
                    elem_int = int(elem_id)
                    elem_data = df_elem[df_elem['Element_ID'] == elem_id].copy()

                    elem_pid = elem_data['Property'].iloc[0] if len(elem_data) > 0 else None
                    elem_pid_int = int(elem_pid) if pd.notna(elem_pid) else None

                    # Filter by Element_Type if exists
                    if 'Element_Type' in elem_data.columns and elem_data['Element_Type'].notna().any():
                        elem_data_sorted = elem_data.sort_values('Allowable', ascending=True)
                        critical_elem_type = elem_data_sorted.iloc[0]['Element_Type']
                        filtered_data = elem_data[elem_data['Element_Type'] == critical_elem_type].copy()

                        fit_data = []
                        thickness_vals = pd.Series(filtered_data['Thickness'].values).dropna().unique()
                        for t in sorted(thickness_vals):
                            t_data = filtered_data[filtered_data['Thickness'] == t]
                            if len(t_data) > 0:
                                fit_data.append({'Thickness': float(t), 'Allowable': float(t_data['Allowable'].min())})
                        fit_df = pd.DataFrame(fit_data)
                    else:
                        fit_data = []
                        thickness_vals = pd.Series(elem_data['Thickness'].values).dropna().unique()
                        for t in sorted(thickness_vals):
                            t_data = elem_data[elem_data['Thickness'] == t]
                            if len(t_data) > 0:
                                fit_data.append({'Thickness': float(t), 'Allowable': float(t_data['Allowable'].min())})
                        fit_df = pd.DataFrame(fit_data)

                    n_pts = len(fit_df)

                    if n_pts < min_data_pts:
                        avg = fit_df['Allowable'].mean() if len(fit_df) > 0 else 0
                        self.allowable_elem_interp[elem_int] = {'a': avg, 'b': 0, 'n_pts': n_pts, 'r2': 0, 'excluded': True, 'property': elem_pid_int}
                        continue

                    try:
                        x = fit_df['Thickness'].values.astype(float)
                        y = fit_df['Allowable'].values.astype(float)
                        valid_mask = (x > 0) & (y > 0)
                        x, y = x[valid_mask], y[valid_mask]

                        if len(x) < 2:
                            self.allowable_elem_interp[elem_int] = {'a': np.mean(y), 'b': 0, 'n_pts': len(x), 'r2': 0, 'excluded': True, 'property': elem_pid_int}
                            continue

                        log_x, log_y = np.log(x), np.log(y)
                        coeffs = np.polyfit(log_x, log_y, 1)
                        b, log_a = coeffs[0], coeffs[1]
                        a = np.exp(log_a)

                        y_pred = a * (x ** b)
                        ss_res = np.sum((y - y_pred) ** 2)
                        ss_tot = np.sum((y - np.mean(y)) ** 2)
                        r2 = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0

                        if r2 < r2_threshold:
                            self.allowable_elem_interp[elem_int] = {'a': np.mean(y), 'b': 0, 'n_pts': n_pts, 'r2': r2, 'excluded': True, 'property': elem_pid_int}
                        else:
                            self.allowable_elem_interp[elem_int] = {'a': a, 'b': b, 'n_pts': n_pts, 'r2': r2, 'excluded': False, 'property': elem_pid_int}
                            valid_elems.append(elem_int)

                    except:
                        self.allowable_elem_interp[elem_int] = {'a': 100, 'b': 0, 'n_pts': n_pts, 'r2': 0, 'excluded': True, 'property': elem_pid_int}

                # Count excluded elements
                excluded_elem_r2 = sum(1 for e in self.allowable_elem_interp.values() if e.get('excluded') and e.get('r2', 0) > 0)
                excluded_elem_data = sum(1 for e in self.allowable_elem_interp.values() if e.get('excluded') and e.get('n_pts', 0) < min_data_pts)

                self.log(f"Valid element fits (R² >= {r2_threshold}): {len(valid_elems)}")
                self.log(f"Excluded elements (R² < {r2_threshold}): {excluded_elem_r2}")
                self.log(f"Excluded elements (data < {min_data_pts}): {excluded_elem_data}")

                if valid_elems:
                    self.log(f"\nSample valid fits (Element):")
                    for eid in valid_elems[:5]:
                        e = self.allowable_elem_interp[eid]
                        self.log(f"  Element {eid}: Allow = {e['a']:.4f} × T^({e['b']:.4f}), R²={e['r2']:.4f}")

            # RF Check v2.1 format status
            n_elem_valid = len(valid_elems) if 'valid_elems' in dir() else 0
            n_elem_excl = len(self.allowable_elem_interp) - n_elem_valid if self.allowable_elem_interp else 0
            self.allow_status.config(text=f"✓ Prop: {len(valid_props)} valid | Elem: {n_elem_valid} valid, {n_elem_excl} excl", foreground="green")

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())
            self.allow_status.config(text="Error", foreground="red")

    def _process_new_allowable_format(self, df):
        """Process format with Element_Type - RF Check v2.1 logic."""
        self.log("  Processing Element_Type format...")

        result_data = []

        # Get unique properties safely
        if 'Property' not in df.columns:
            self.log("  WARNING: No 'Property' column found")
            return pd.DataFrame(result_data)

        properties = pd.Series(df['Property'].values).dropna().unique()

        for pid in properties:
            prop_df = df[df['Property'] == pid].copy()
            if len(prop_df) == 0:
                continue

            prop_df_sorted = prop_df.sort_values('Allowable', ascending=True)
            critical_row = prop_df_sorted.iloc[0]

            crit_elem_id = critical_row.get('Element_ID', None)
            crit_elem_type = critical_row.get('Element_Type', None)

            if crit_elem_id is not None and crit_elem_type is not None:
                try:
                    crit_id = int(crit_elem_id)
                    mask = (prop_df['Element_ID'].astype(float).astype(int) == crit_id) & (prop_df['Element_Type'] == crit_elem_type)
                    filtered_df = prop_df[mask].copy()
                except:
                    filtered_df = prop_df.copy()
            elif crit_elem_type is not None:
                filtered_df = prop_df[prop_df['Element_Type'] == crit_elem_type].copy()
            else:
                filtered_df = prop_df.copy()

            # Get unique thicknesses safely (avoid DataFrame.unique() issue)
            if 'Thickness' not in filtered_df.columns or len(filtered_df) == 0:
                continue

            thickness_values = pd.Series(filtered_df['Thickness'].values).dropna().unique()

            for t in sorted(thickness_values):
                t_data = filtered_df[filtered_df['Thickness'] == t]
                if len(t_data) > 0:
                    min_allow = t_data['Allowable'].min()
                    result_data.append({'Property': int(pid), 'Thickness': float(t), 'Allowable': float(min_allow)})

        self.log(f"  Processed: {len(properties)} properties -> {len(result_data)} data points")
        return pd.DataFrame(result_data)

    def load_element_ids(self):
        path = self.element_excel_path.get()
        if not path:
            return

        self.log("\n" + "="*70)
        self.log("LOADING ELEMENT IDs FOR OFFSET")
        self.log("="*70)

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

            self.elem_status.config(text=f"✓ Landing: {len(self.landing_elem_ids)}, Bar: {len(self.bar_offset_elem_ids)}", foreground="green")

        except Exception as e:
            self.log(f"ERROR: {e}")
            self.elem_status.config(text="Error", foreground="red")

    def load_residual_strength(self):
        """Load Residual Strength Excel for stress combination - RF Check Tool logic."""
        path = self.residual_strength_path.get()
        if not path or not os.path.exists(path):
            messagebox.showerror("Error", "Select Residual Strength Excel file")
            return

        self.log("\n" + "="*70)
        self.log("LOADING RESIDUAL STRENGTH DATA")
        self.log("="*70)

        try:
            xl = pd.ExcelFile(path)
            self.log(f"Sheets: {xl.sheet_names}")

            # Find Residual Strength sheet (RF Check Tool logic)
            res_sh = None
            for sheet in xl.sheet_names:
                sl = sheet.lower().replace(' ', '').replace('_', '')
                if sl == 'residualstrength' or sl == 'residual strength':
                    res_sh = sheet
                    break

            # Fallback - search for sheets containing 'residual' or 'strength'
            if not res_sh:
                for sheet in xl.sheet_names:
                    sl = sheet.lower()
                    if 'residual' in sl or 'strength' in sl:
                        res_sh = sheet
                        break

            if not res_sh:
                # Use first sheet if no specific sheet found
                res_sh = xl.sheet_names[0]
                self.log(f"  No 'Residual Strength' sheet found, using: {res_sh}")
            else:
                self.log(f"  Found Residual Strength sheet: {res_sh}")

            self.residual_strength_df = pd.read_excel(xl, sheet_name=res_sh)
            self.log(f"  Loaded {len(self.residual_strength_df)} rows")
            self.log(f"  Columns: {list(self.residual_strength_df.columns)}")

            # Parse combination table structure (first col = Combined LC, then pairs of Case/Mult)
            cols = self.residual_strength_df.columns.tolist()
            comb_col = cols[0]
            self.log(f"  Combined LC column: {comb_col}")

            # Find Case ID + Multiplier column pairs
            self.combination_table = []
            i = 1
            while i < len(cols) - 1:
                col_name = str(cols[i]).upper()
                next_col_name = str(cols[i+1]).upper()
                if ('CASE' in col_name or 'ID' in col_name) and 'MULT' in next_col_name:
                    self.combination_table.append((cols[i], cols[i+1]))
                    self.log(f"    Found pair: {cols[i]} + {cols[i+1]}")
                    i += 2
                else:
                    i += 1

            self.log(f"  Total combination pairs: {len(self.combination_table)}")
            self.resid_status.config(text=f"✓ {len(self.residual_strength_df)} rows, {len(self.combination_table)} pairs", foreground="green")

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())
            self.resid_status.config(text="Error", foreground="red")

    # ==================== HELPER FUNCTIONS ====================
    def get_allowable_stress(self, pid, thickness):
        pid_int = int(pid)
        if pid_int not in self.allowable_interp:
            return None
        params = self.allowable_interp[pid_int]
        if params.get('excluded', False) and params['b'] == 0:
            return params['a']
        return params['a'] * (thickness ** params['b'])

    def get_allowable_stress_elem(self, elem_id, thickness):
        elem_int = int(elem_id)
        if elem_int not in self.allowable_elem_interp:
            return None
        params = self.allowable_elem_interp[elem_int]
        if params.get('excluded', False) and params['b'] == 0:
            return params['a']
        return params['a'] * (thickness ** params['b'])

    def get_required_thickness(self, pid, stress, min_rf=1.0):
        pid_int = int(pid)
        if pid_int not in self.allowable_interp:
            return None
        params = self.allowable_interp[pid_int]
        a, b = params['a'], params['b']
        if params.get('excluded', False) or b == 0:
            return None
        required_allow = abs(stress) * min_rf
        if a <= 0:
            return None
        try:
            ratio = required_allow / a
            if ratio <= 0:
                return None
            t_req = ratio ** (1.0 / b)
            return t_req if 0 < t_req < 1000 else None
        except:
            return None

    def get_density(self, pid):
        """Get density from property's material (MAT1/MAT8/MAT9/etc.)"""
        if pid in self.prop_to_material:
            mid = self.prop_to_material[pid]
            if mid in self.material_densities:
                return self.material_densities[mid]
        return 2.7e-9  # Default aluminum

    # ==================== OPTIMIZATION ====================
    def start_optimization(self):
        if not self.bdf_model:
            messagebox.showerror("Error", "Load BDF first")
            return
        if not self.allowable_interp:
            messagebox.showerror("Error", "Load allowable data first")
            return

        self.is_running = True
        self.btn_start.config(state=tk.DISABLED)
        self.btn_stop.config(state=tk.NORMAL)
        self.iteration_results = []
        self.best_solution = None

        # Route to selected algorithm
        algo = self.algorithm_var.get()
        if algo == "Simple Iterative":
            threading.Thread(target=self._run_simple_iterative, daemon=True).start()
        elif algo == "Fast GA (Surrogate)":
            threading.Thread(target=self._run_fast_ga, daemon=True).start()
        elif algo == "Full GA + Nastran":
            threading.Thread(target=self._run_full_ga_nastran, daemon=True).start()
        elif algo == "Surrogate-Assisted GA":
            threading.Thread(target=self._run_surrogate_assisted_ga, daemon=True).start()
        elif algo == "RSM + SQP":
            threading.Thread(target=self._run_rsm_sqp, daemon=True).start()
        elif algo == "Hybrid GA + Nastran":
            threading.Thread(target=self._run_hybrid_ga, daemon=True).start()
        elif algo == "Top-Down (Max to Target)":
            threading.Thread(target=self._run_topdown_algorithm, daemon=True).start()
        elif algo == "Bottom-Up (Min to Target)":
            threading.Thread(target=self._run_bottomup_algorithm, daemon=True).start()
        else:
            threading.Thread(target=self._run_simple_iterative, daemon=True).start()

    def stop_optimization(self):
        self.is_running = False
        self.log("\n*** STOPPING ***")

    def _run_simple_iterative(self):
        """Algorithm 1: Simple Iterative - increase failing, decrease over-designed."""
        try:
            self.log("\n" + "="*70)
            self.log("ALGORITHM: SIMPLE ITERATIVE")
            self.log("="*70)

            bar_min = float(self.bar_min_thickness.get())
            bar_max = float(self.bar_max_thickness.get())
            skin_min = float(self.skin_min_thickness.get())
            skin_max = float(self.skin_max_thickness.get())
            step = float(self.thickness_step.get())
            target_rf = float(self.target_rf.get())
            rf_tol = float(self.rf_tolerance.get())
            max_iter = int(self.max_iterations.get())

            self.log(f"\nBar range: {bar_min}-{bar_max} mm")
            self.log(f"Skin range: {skin_min}-{skin_max} mm")
            self.log(f"Target RF: {target_rf} ± {rf_tol}")
            self.log(f"Max iterations: {max_iter}")

            # Initialize all properties to minimum
            for pid in self.bar_properties:
                self.current_bar_thicknesses[pid] = bar_min
            for pid in self.skin_properties:
                self.current_skin_thicknesses[pid] = skin_min

            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            base_folder = os.path.join(self.output_folder.get(), f"opt_{timestamp}")
            os.makedirs(base_folder, exist_ok=True)

            iteration = 0
            best_weight = float('inf')

            while iteration < max_iter and self.is_running:
                iteration += 1
                self.log(f"\n{'='*60}")
                self.log(f"ITERATION {iteration}")
                self.log(f"{'='*60}")

                self.update_progress((iteration/max_iter)*100, f"Iteration {iteration}/{max_iter}")

                iter_folder = os.path.join(base_folder, f"iter_{iteration:03d}")
                os.makedirs(iter_folder, exist_ok=True)

                # Run iteration
                result = self._run_iteration(iter_folder, iteration, target_rf)

                if not result:
                    self.log("  Iteration failed, increasing all thicknesses...")
                    for pid in self.current_bar_thicknesses:
                        self.current_bar_thicknesses[pid] = min(self.current_bar_thicknesses[pid] + step, bar_max)
                    for pid in self.current_skin_thicknesses:
                        self.current_skin_thicknesses[pid] = min(self.current_skin_thicknesses[pid] + step, skin_max)
                    continue

                self.iteration_results.append(result)

                # Check for best
                if result['min_rf'] >= target_rf - rf_tol and result['weight'] < best_weight:
                    best_weight = result['weight']
                    self.best_solution = result.copy()
                    self.log(f"\n  *** NEW BEST: Weight={best_weight:.6f}t, RF={result['min_rf']:.4f} ***")

                # Per-property update based on RF
                self._smart_thickness_update(result, step, bar_min, bar_max, skin_min, skin_max, target_rf, rf_tol)

            # Summary
            self.log("\n" + "="*70)
            self.log("OPTIMIZATION COMPLETE")
            self.log("="*70)

            if self.best_solution:
                self.log(f"\nBest: Weight={self.best_solution['weight']:.6f}t, RF={self.best_solution['min_rf']:.4f}")
                self._update_ui()

            self._save_results(base_folder)
            self._generate_final_report(base_folder, "Simple Iterative", nastran_count=iteration)

            self.root.after(0, lambda: messagebox.showinfo("Done", f"Complete!\nIterations: {iteration}\nBest weight: {best_weight:.6f}t"))

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())

        finally:
            self.is_running = False
            self.root.after(0, lambda: [self.btn_start.config(state=tk.NORMAL), self.btn_stop.config(state=tk.DISABLED)])

    # ==================== FAST GA (SURROGATE MODEL) ====================
    def _run_fast_ga(self):
        """Algorithm 2: Fast GA with surrogate model (no Nastran during optimization)."""
        try:
            self.log("\n" + "="*70)
            self.log("ALGORITHM: FAST GA (SURROGATE MODEL)")
            self.log("="*70)

            # Parameters
            bar_min = float(self.bar_min_thickness.get())
            bar_max = float(self.bar_max_thickness.get())
            skin_min = float(self.skin_min_thickness.get())
            skin_max = float(self.skin_max_thickness.get())
            target_rf = float(self.target_rf.get())
            rf_tol = float(self.rf_tolerance.get())

            pop_size = int(self.ga_population.get())
            n_generations = int(self.ga_generations.get())
            mutation_rate = float(self.ga_mutation_rate.get())
            crossover_rate = float(self.ga_crossover_rate.get())

            self.log(f"\nGA Parameters:")
            self.log(f"  Population: {pop_size}")
            self.log(f"  Generations: {n_generations}")
            self.log(f"  Mutation Rate: {mutation_rate}")
            self.log(f"  Crossover Rate: {crossover_rate}")
            self.log(f"\nTarget RF: {target_rf} ± {rf_tol}")

            # Create chromosome structure
            bar_pids = list(self.bar_properties.keys())
            skin_pids = list(self.skin_properties.keys())
            n_bars = len(bar_pids)
            n_skins = len(skin_pids)
            n_genes = n_bars + n_skins

            self.log(f"\nChromosome: {n_bars} bar + {n_skins} skin = {n_genes} genes")

            if n_genes == 0:
                self.log("ERROR: No properties to optimize!")
                return

            # Initialize reference stresses (using average from allowable data)
            self._init_reference_stresses(bar_pids, skin_pids, bar_min, skin_min)

            # Initialize population
            population = []
            for _ in range(pop_size):
                chromosome = []
                # Bar thicknesses
                for pid in bar_pids:
                    chromosome.append(random.uniform(bar_min, bar_max))
                # Skin thicknesses
                for pid in skin_pids:
                    chromosome.append(random.uniform(skin_min, skin_max))
                population.append(chromosome)

            # Evolution
            best_fitness = float('inf')
            best_chromosome = None
            fitness_history = []

            for gen in range(n_generations):
                if not self.is_running:
                    break

                # Evaluate fitness
                fitness_values = []
                for chromosome in population:
                    fit = self._evaluate_surrogate_fitness(
                        chromosome, bar_pids, skin_pids,
                        bar_min, bar_max, skin_min, skin_max,
                        target_rf, rf_tol
                    )
                    fitness_values.append(fit)

                # Find best
                min_fit_idx = fitness_values.index(min(fitness_values))
                if fitness_values[min_fit_idx] < best_fitness:
                    best_fitness = fitness_values[min_fit_idx]
                    best_chromosome = population[min_fit_idx].copy()

                fitness_history.append(best_fitness)

                # Progress update
                if gen % 10 == 0 or gen == n_generations - 1:
                    self.update_progress((gen / n_generations) * 100, f"Generation {gen}/{n_generations}")
                    self.log(f"Gen {gen}: Best Fitness = {best_fitness:.6f}")

                # Selection (Tournament)
                new_population = []
                while len(new_population) < pop_size:
                    # Tournament selection
                    idx1, idx2 = random.sample(range(pop_size), 2)
                    parent1 = population[idx1] if fitness_values[idx1] < fitness_values[idx2] else population[idx2]

                    idx3, idx4 = random.sample(range(pop_size), 2)
                    parent2 = population[idx3] if fitness_values[idx3] < fitness_values[idx4] else population[idx4]

                    # Crossover (BLX-alpha)
                    if random.random() < crossover_rate:
                        child = self._blx_crossover(parent1, parent2, alpha=0.5)
                    else:
                        child = parent1.copy()

                    # Mutation (Gaussian)
                    child = self._gaussian_mutation(
                        child, mutation_rate, n_bars,
                        bar_min, bar_max, skin_min, skin_max
                    )

                    new_population.append(child)

                population = new_population

            # Apply best solution
            if best_chromosome:
                for i, pid in enumerate(bar_pids):
                    self.current_bar_thicknesses[pid] = best_chromosome[i]
                for i, pid in enumerate(skin_pids):
                    self.current_skin_thicknesses[pid] = best_chromosome[n_bars + i]

                # Calculate final weight and RF
                weight = self._calculate_weight()
                min_rf = self._estimate_min_rf(best_chromosome, bar_pids, skin_pids)

                self.best_solution = {
                    'iteration': n_generations,
                    'min_rf': min_rf,
                    'weight': weight,
                    'bar_thicknesses': self.current_bar_thicknesses.copy(),
                    'skin_thicknesses': self.current_skin_thicknesses.copy(),
                    'n_fail': 0 if min_rf >= target_rf else 1
                }

                self.log("\n" + "="*70)
                self.log("FAST GA COMPLETE")
                self.log("="*70)
                self.log(f"\nBest Solution:")
                self.log(f"  Weight: {weight:.6f} tonnes")
                self.log(f"  Estimated Min RF: {min_rf:.4f}")
                self.log(f"  Fitness: {best_fitness:.6f}")

                self._update_ui()

                # Save results
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                base_folder = os.path.join(self.output_folder.get(), f"fast_ga_{timestamp}")
                os.makedirs(base_folder, exist_ok=True)
                self._save_results(base_folder)
                self._generate_final_report(base_folder, "Fast GA (Surrogate)",
                    extra_info={"Note": "Results based on surrogate model - run Nastran to verify"})

                self.root.after(0, lambda: messagebox.showinfo(
                    "Fast GA Complete",
                    f"Optimization finished!\n\nWeight: {weight:.6f}t\nEstimated RF: {min_rf:.4f}\n\nNote: Run Nastran to verify results."
                ))

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())

        finally:
            self.is_running = False
            self.root.after(0, lambda: [self.btn_start.config(state=tk.NORMAL), self.btn_stop.config(state=tk.DISABLED)])

    def _init_reference_stresses(self, bar_pids, skin_pids, bar_ref_t, skin_ref_t):
        """Initialize reference stresses for surrogate model."""
        self.reference_stresses = {}
        self.reference_thickness = {}

        # For bars - estimate stress from allowable curve (assuming RF=1 at some thickness)
        for pid in bar_pids:
            if pid in self.allowable_interp:
                params = self.allowable_interp[pid]
                # Reference: at min thickness, stress ≈ allowable (RF=1)
                ref_allow = params['a'] * (bar_ref_t ** params['b'])
                self.reference_stresses[pid] = ref_allow  # Stress = Allowable when RF=1
                self.reference_thickness[pid] = bar_ref_t
            else:
                self.reference_stresses[pid] = 100.0  # Default
                self.reference_thickness[pid] = bar_ref_t

        # For skins
        for pid in skin_pids:
            if pid in self.allowable_interp:
                params = self.allowable_interp[pid]
                ref_allow = params['a'] * (skin_ref_t ** params['b'])
                self.reference_stresses[pid] = ref_allow
                self.reference_thickness[pid] = skin_ref_t
            else:
                self.reference_stresses[pid] = 100.0
                self.reference_thickness[pid] = skin_ref_t

    def _evaluate_surrogate_fitness(self, chromosome, bar_pids, skin_pids,
                                     bar_min, bar_max, skin_min, skin_max,
                                     target_rf, rf_tol):
        """Evaluate fitness using surrogate model (no Nastran)."""
        n_bars = len(bar_pids)

        # Calculate weight
        weight = 0.0

        # Bar weight
        for i, pid in enumerate(bar_pids):
            dim1 = chromosome[i]  # Optimized dimension
            # Use BDF PBARL dim2 (original geometry), fallback to Excel
            if pid in self.pbarl_dims:
                dim2 = self.pbarl_dims[pid]['dim2']
            else:
                dim2 = self.bar_properties[pid].get('dim2', dim1)
            rho = self.get_density(pid)
            if pid in self.prop_elements:
                length = sum(self.bar_lengths.get(eid, 0) for eid in self.prop_elements[pid])
                weight += length * dim1 * dim2 * rho

        # Skin weight
        for i, pid in enumerate(skin_pids):
            t = chromosome[n_bars + i]
            rho = self.get_density(pid)
            if pid in self.prop_elements:
                area = sum(self.element_areas.get(eid, 0) for eid in self.prop_elements[pid])
                weight += area * t * rho

        # Calculate RF penalty using surrogate model
        penalty = 0.0
        penalty_factor = 1000.0  # Large penalty for constraint violation

        # Bar RF
        for i, pid in enumerate(bar_pids):
            t = chromosome[i]
            rf = self._estimate_rf_surrogate(pid, t, is_bar=True)
            if rf < target_rf:
                penalty += penalty_factor * (target_rf - rf) ** 2

        # Skin RF
        for i, pid in enumerate(skin_pids):
            t = chromosome[n_bars + i]
            rf = self._estimate_rf_surrogate(pid, t, is_bar=False)
            if rf < target_rf:
                penalty += penalty_factor * (target_rf - rf) ** 2

        return weight + penalty

    def _estimate_rf_surrogate(self, pid, thickness, is_bar=True):
        """Estimate RF using surrogate model: Stress scales with thickness."""
        if pid not in self.allowable_interp:
            return 1.0  # Default pass

        params = self.allowable_interp[pid]
        allowable = params['a'] * (thickness ** params['b'])

        # Stress scaling: Stress ∝ 1/t^α (α=1.0 for bars, 1.5 for skins)
        alpha = 1.0 if is_bar else 1.5
        ref_stress = self.reference_stresses.get(pid, 100.0)
        ref_t = self.reference_thickness.get(pid, thickness)

        if ref_t > 0 and thickness > 0:
            stress = ref_stress * (ref_t / thickness) ** alpha
        else:
            stress = ref_stress

        if stress > 0:
            return allowable / stress
        return 999.0

    def _estimate_min_rf(self, chromosome, bar_pids, skin_pids):
        """Estimate minimum RF from chromosome."""
        min_rf = 999.0
        n_bars = len(bar_pids)

        for i, pid in enumerate(bar_pids):
            rf = self._estimate_rf_surrogate(pid, chromosome[i], is_bar=True)
            min_rf = min(min_rf, rf)

        for i, pid in enumerate(skin_pids):
            rf = self._estimate_rf_surrogate(pid, chromosome[n_bars + i], is_bar=False)
            min_rf = min(min_rf, rf)

        return min_rf

    def _blx_crossover(self, parent1, parent2, alpha=0.5):
        """BLX-alpha crossover for real-valued chromosomes with bounds check."""
        child = []
        for g1, g2 in zip(parent1, parent2):
            min_g, max_g = min(g1, g2), max(g1, g2)
            range_g = max_g - min_g
            # Generate child gene
            new_val = random.uniform(min_g - alpha * range_g, max_g + alpha * range_g)
            # Ensure positive (will be bounded later in mutation)
            child.append(max(0.1, new_val))  # Never negative!
        return child

    def _gaussian_mutation(self, chromosome, mutation_rate, n_bars,
                           bar_min, bar_max, skin_min, skin_max):
        """Gaussian mutation with STRICT bounds enforcement."""
        mutated = chromosome.copy()
        for i in range(len(mutated)):
            if random.random() < mutation_rate:
                if i < n_bars:
                    # Bar gene
                    sigma = (bar_max - bar_min) * 0.1
                    mutated[i] += random.gauss(0, sigma)
                    # STRICT bounds - never negative!
                    mutated[i] = max(bar_min, min(bar_max, mutated[i]))
                else:
                    # Skin gene
                    sigma = (skin_max - skin_min) * 0.1
                    mutated[i] += random.gauss(0, sigma)
                    # STRICT bounds - never negative!
                    mutated[i] = max(skin_min, min(skin_max, mutated[i]))
            else:
                # Even without mutation, enforce bounds (for crossover results)
                if i < n_bars:
                    mutated[i] = max(bar_min, min(bar_max, mutated[i]))
                else:
                    mutated[i] = max(skin_min, min(skin_max, mutated[i]))
        return mutated

    # ==================== HYBRID GA + NASTRAN ====================
    def _run_hybrid_ga(self):
        """Algorithm 3: Hybrid GA - Fast GA first, then Nastran validation."""
        try:
            self.log("\n" + "="*70)
            self.log("ALGORITHM: HYBRID GA + NASTRAN")
            self.log("="*70)

            # Phase 1: Run Fast GA
            self.log("\n>>> PHASE 1: Fast GA Optimization <<<")
            self._run_fast_ga_internal()

            if not self.is_running:
                return

            # Phase 2: Nastran validation of best solutions
            self.log("\n>>> PHASE 2: Nastran Validation <<<")

            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            base_folder = os.path.join(self.output_folder.get(), f"hybrid_ga_{timestamp}")
            os.makedirs(base_folder, exist_ok=True)

            target_rf = float(self.target_rf.get())

            # Run Nastran with best solution
            self.log("\nValidating best solution with Nastran...")
            iter_folder = os.path.join(base_folder, "validation")
            os.makedirs(iter_folder, exist_ok=True)

            result = self._run_iteration(iter_folder, 1, target_rf)

            if result:
                self.best_solution = result
                self.log(f"\nNastran Validation Results:")
                self.log(f"  Actual Min RF: {result['min_rf']:.4f}")
                self.log(f"  Actual Weight: {result['weight']:.6f}t")
                self.log(f"  Failures: {result['n_fail']}")

                self._update_ui()
                self._save_results(base_folder)
                self._generate_final_report(base_folder, "Hybrid GA + Nastran", nastran_count=1,
                    extra_info={"Phase 1": "Fast GA (Surrogate)", "Phase 2": "Nastran Validation"})

                self.root.after(0, lambda: messagebox.showinfo(
                    "Hybrid GA Complete",
                    f"Optimization finished!\n\nWeight: {result['weight']:.6f}t\nActual RF: {result['min_rf']:.4f}\nFailures: {result['n_fail']}"
                ))
            else:
                self.log("ERROR: Nastran validation failed!")

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())

        finally:
            self.is_running = False
            self.root.after(0, lambda: [self.btn_start.config(state=tk.NORMAL), self.btn_stop.config(state=tk.DISABLED)])

    def _run_full_ga_nastran(self):
        """Algorithm 4: Full GA with Nastran - runs Nastran for every fitness evaluation."""
        try:
            self.log("\n" + "="*70)
            self.log("ALGORITHM: FULL GA + NASTRAN")
            self.log("(Runs Nastran for every fitness evaluation - SLOW but ACCURATE)")
            self.log("="*70)

            # Parameters
            bar_min = float(self.bar_min_thickness.get())
            bar_max = float(self.bar_max_thickness.get())
            skin_min = float(self.skin_min_thickness.get())
            skin_max = float(self.skin_max_thickness.get())
            target_rf = float(self.target_rf.get())
            rf_tol = float(self.rf_tolerance.get())

            pop_size = int(self.ga_population.get())
            n_generations = int(self.ga_generations.get())
            mutation_rate = float(self.ga_mutation_rate.get())
            crossover_rate = float(self.ga_crossover_rate.get())

            self.log(f"\nGA Parameters:")
            self.log(f"  Population: {pop_size}")
            self.log(f"  Generations: {n_generations}")
            self.log(f"  Mutation Rate: {mutation_rate}")
            self.log(f"  Crossover Rate: {crossover_rate}")
            self.log(f"\nTarget RF: {target_rf} ± {rf_tol}")
            self.log(f"\nWARNING: This will run {pop_size * n_generations} Nastran analyses!")

            bar_pids = list(self.bar_properties.keys())
            skin_pids = list(self.skin_properties.keys())
            n_bars = len(bar_pids)
            n_skins = len(skin_pids)
            n_genes = n_bars + n_skins

            if n_genes == 0:
                self.log("ERROR: No properties to optimize!")
                return

            self.log(f"\nChromosome: {n_bars} bars + {n_skins} skins = {n_genes} genes")

            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            base_folder = os.path.join(self.output_folder.get(), f"full_ga_{timestamp}")
            os.makedirs(base_folder, exist_ok=True)

            # Initialize population
            population = []
            for _ in range(pop_size):
                chromosome = []
                for pid in bar_pids:
                    chromosome.append(random.uniform(bar_min, bar_max))
                for pid in skin_pids:
                    chromosome.append(random.uniform(skin_min, skin_max))
                population.append(chromosome)

            best_fitness = float('-inf')
            best_chromosome = None
            best_result = None
            eval_count = 0

            for gen in range(n_generations):
                if not self.is_running:
                    break

                self.log(f"\n{'='*50}")
                self.log(f"GENERATION {gen+1}/{n_generations}")
                self.log(f"{'='*50}")

                self.update_progress((gen/n_generations)*100, f"Gen {gen+1}/{n_generations}")

                # Evaluate fitness for each individual using Nastran
                fitness_scores = []
                for idx, chromosome in enumerate(population):
                    if not self.is_running:
                        break

                    eval_count += 1
                    self.log(f"\n  Individual {idx+1}/{pop_size} (Eval #{eval_count})")

                    # Set thicknesses from chromosome
                    for i, pid in enumerate(bar_pids):
                        self.current_bar_thicknesses[pid] = max(bar_min, min(bar_max, chromosome[i]))
                    for i, pid in enumerate(skin_pids):
                        self.current_skin_thicknesses[pid] = max(skin_min, min(skin_max, chromosome[n_bars + i]))

                    # Run Nastran
                    iter_folder = os.path.join(base_folder, f"gen_{gen+1:03d}_ind_{idx+1:03d}")
                    os.makedirs(iter_folder, exist_ok=True)

                    result = self._run_iteration(iter_folder, eval_count, target_rf)

                    if result:
                        min_rf = result['min_rf']
                        weight = result['weight']

                        # Fitness: minimize weight, penalize RF < target
                        if min_rf >= target_rf - rf_tol:
                            fitness = 1000.0 / (weight + 0.001)  # Higher is better
                        else:
                            # Penalty for failing RF
                            penalty = (target_rf - min_rf) * 100
                            fitness = 1000.0 / (weight + 0.001) - penalty

                        fitness_scores.append(fitness)
                        self.log(f"    RF={min_rf:.4f}, Weight={weight:.6f}t, Fitness={fitness:.2f}")

                        # Track best
                        if fitness > best_fitness:
                            best_fitness = fitness
                            best_chromosome = chromosome.copy()
                            best_result = result
                            self.best_solution = result
                            self.log(f"    *** NEW BEST! ***")
                    else:
                        fitness_scores.append(-1000)  # Failed evaluation
                        self.log(f"    FAILED!")

                if not self.is_running or len(fitness_scores) < pop_size:
                    break

                # Selection (Tournament)
                def tournament_select(pop, fit, k=3):
                    selected = random.sample(list(zip(pop, fit)), k)
                    return max(selected, key=lambda x: x[1])[0]

                # Create new population
                new_population = []

                # Elitism - keep best individual
                if best_chromosome:
                    new_population.append(best_chromosome.copy())

                while len(new_population) < pop_size:
                    # Select parents
                    parent1 = tournament_select(population, fitness_scores)
                    parent2 = tournament_select(population, fitness_scores)

                    # Crossover (BLX-α)
                    if random.random() < crossover_rate:
                        child = []
                        alpha = 0.5
                        for g1, g2 in zip(parent1, parent2):
                            d = abs(g2 - g1)
                            low = max(bar_min if len(child) < n_bars else skin_min, min(g1, g2) - alpha * d)
                            high = min(bar_max if len(child) < n_bars else skin_max, max(g1, g2) + alpha * d)
                            child.append(random.uniform(low, high))
                    else:
                        child = parent1.copy()

                    # Mutation (Gaussian)
                    for i in range(len(child)):
                        if random.random() < mutation_rate:
                            if i < n_bars:
                                sigma = (bar_max - bar_min) * 0.1
                                child[i] = max(bar_min, min(bar_max, child[i] + random.gauss(0, sigma)))
                            else:
                                sigma = (skin_max - skin_min) * 0.1
                                child[i] = max(skin_min, min(skin_max, child[i] + random.gauss(0, sigma)))

                    new_population.append(child)

                population = new_population[:pop_size]

                # Log generation summary
                valid_fitness = [f for f in fitness_scores if f > -500]
                if valid_fitness:
                    self.log(f"\n  Gen {gen+1} Summary: Best Fitness={max(valid_fitness):.2f}, Avg={sum(valid_fitness)/len(valid_fitness):.2f}")

            # Final results
            self.log("\n" + "="*70)
            self.log("FULL GA + NASTRAN COMPLETE")
            self.log("="*70)
            self.log(f"Total Nastran evaluations: {eval_count}")

            if best_result:
                # Set final thicknesses
                for i, pid in enumerate(bar_pids):
                    self.current_bar_thicknesses[pid] = best_chromosome[i]
                for i, pid in enumerate(skin_pids):
                    self.current_skin_thicknesses[pid] = best_chromosome[n_bars + i]

                self.log(f"\nBest Solution:")
                self.log(f"  Min RF: {best_result['min_rf']:.4f}")
                self.log(f"  Weight: {best_result['weight']:.6f}t")
                self.log(f"  Failures: {best_result['n_fail']}")

                self._update_ui()
                self._save_results(base_folder)
                self._generate_final_report(base_folder, "Full GA + Nastran", nastran_count=eval_count,
                    extra_info={"Population": pop_size, "Generations": n_generations})

                self.root.after(0, lambda: messagebox.showinfo(
                    "Full GA Complete",
                    f"Optimization finished!\n\nTotal Evaluations: {eval_count}\nWeight: {best_result['weight']:.6f}t\nMin RF: {best_result['min_rf']:.4f}\nFailures: {best_result['n_fail']}"
                ))
            else:
                self.log("ERROR: No valid solution found!")

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())

        finally:
            self.is_running = False
            self.root.after(0, lambda: [self.btn_start.config(state=tk.NORMAL), self.btn_stop.config(state=tk.DISABLED)])

    def _run_surrogate_assisted_ga(self):
        """Algorithm 5: Surrogate-Assisted GA - learns from previous Nastran runs."""
        try:
            self.log("\n" + "="*70)
            self.log("ALGORITHM: SURROGATE-ASSISTED GA")
            self.log("(Learns from Nastran results - SMART & EFFICIENT)")
            self.log("="*70)

            # Parameters
            bar_min = float(self.bar_min_thickness.get())
            bar_max = float(self.bar_max_thickness.get())
            skin_min = float(self.skin_min_thickness.get())
            skin_max = float(self.skin_max_thickness.get())
            target_rf = float(self.target_rf.get())
            rf_tol = float(self.rf_tolerance.get())

            pop_size = int(self.ga_population.get())
            n_generations = int(self.ga_generations.get())
            mutation_rate = float(self.ga_mutation_rate.get())
            crossover_rate = float(self.ga_crossover_rate.get())

            # Surrogate parameters
            initial_samples = min(pop_size, 20)  # Initial Nastran runs to build surrogate
            nastran_per_gen = max(3, pop_size // 10)  # Nastran runs per generation for update

            self.log(f"\nGA Parameters:")
            self.log(f"  Population: {pop_size}")
            self.log(f"  Generations: {n_generations}")
            self.log(f"  Mutation Rate: {mutation_rate}")
            self.log(f"  Crossover Rate: {crossover_rate}")
            self.log(f"\nSurrogate Parameters:")
            self.log(f"  Initial Nastran samples: {initial_samples}")
            self.log(f"  Nastran updates per generation: {nastran_per_gen}")
            self.log(f"\nEstimated total Nastran runs: {initial_samples + n_generations * nastran_per_gen}")
            self.log(f"(vs Full GA: {pop_size * n_generations})")

            bar_pids = list(self.bar_properties.keys())
            skin_pids = list(self.skin_properties.keys())
            n_bars = len(bar_pids)
            n_skins = len(skin_pids)
            n_genes = n_bars + n_skins

            if n_genes == 0:
                self.log("ERROR: No properties to optimize!")
                return

            self.log(f"\nChromosome: {n_bars} bars + {n_skins} skins = {n_genes} genes")

            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            base_folder = os.path.join(self.output_folder.get(), f"surrogate_ga_{timestamp}")
            os.makedirs(base_folder, exist_ok=True)

            # ========== PHASE 1: Initial Sampling (Latin Hypercube-like) ==========
            self.log("\n" + "="*50)
            self.log("PHASE 1: Building Initial Surrogate Model")
            self.log("="*50)

            # Storage for surrogate training data
            X_train = []  # Chromosomes (inputs)
            y_rf_train = []  # Min RF values (outputs)
            y_weight_train = []  # Weight values (outputs)

            # Generate initial samples using stratified random sampling
            initial_population = []
            for i in range(initial_samples):
                chromosome = []
                for j, pid in enumerate(bar_pids):
                    # Stratified: divide range into initial_samples parts
                    low = bar_min + (bar_max - bar_min) * (i / initial_samples)
                    high = bar_min + (bar_max - bar_min) * ((i + 1) / initial_samples)
                    chromosome.append(random.uniform(low, high))
                for j, pid in enumerate(skin_pids):
                    low = skin_min + (skin_max - skin_min) * (i / initial_samples)
                    high = skin_min + (skin_max - skin_min) * ((i + 1) / initial_samples)
                    chromosome.append(random.uniform(low, high))
                # Shuffle to avoid correlation
                random.shuffle(chromosome[:n_bars])
                if n_skins > 0:
                    random.shuffle(chromosome[n_bars:])
                initial_population.append(chromosome)

            # Run Nastran for initial samples
            nastran_count = 0
            best_fitness = float('-inf')
            best_chromosome = None
            best_result = None

            for idx, chromosome in enumerate(initial_population):
                if not self.is_running:
                    break

                nastran_count += 1
                self.log(f"\n  Initial Sample {idx+1}/{initial_samples} (Nastran #{nastran_count})")
                self.update_progress((idx/initial_samples)*20, f"Initial sampling {idx+1}/{initial_samples}")

                # Set thicknesses
                for i, pid in enumerate(bar_pids):
                    self.current_bar_thicknesses[pid] = chromosome[i]
                for i, pid in enumerate(skin_pids):
                    self.current_skin_thicknesses[pid] = chromosome[n_bars + i]

                # Run Nastran
                iter_folder = os.path.join(base_folder, f"init_{idx+1:03d}")
                os.makedirs(iter_folder, exist_ok=True)
                result = self._run_iteration(iter_folder, nastran_count, target_rf)

                if result:
                    min_rf = result['min_rf']
                    weight = result['weight']

                    X_train.append(chromosome)
                    y_rf_train.append(min_rf)
                    y_weight_train.append(weight)

                    # Calculate fitness
                    if min_rf >= target_rf - rf_tol:
                        fitness = 1000.0 / (weight + 0.001)
                    else:
                        penalty = (target_rf - min_rf) * 100
                        fitness = 1000.0 / (weight + 0.001) - penalty

                    self.log(f"    RF={min_rf:.4f}, Weight={weight:.6f}t, Fitness={fitness:.2f}")

                    if fitness > best_fitness:
                        best_fitness = fitness
                        best_chromosome = chromosome.copy()
                        best_result = result
                        self.best_solution = result
                        self.log(f"    *** NEW BEST! ***")

            if len(X_train) < 3:
                self.log("ERROR: Not enough initial samples!")
                return

            self.log(f"\n  Surrogate built with {len(X_train)} samples")

            # ========== PHASE 2: GA with Surrogate ==========
            self.log("\n" + "="*50)
            self.log("PHASE 2: Surrogate-Assisted Optimization")
            self.log("="*50)

            # Initialize population (include best from initial + random)
            population = []
            if best_chromosome:
                population.append(best_chromosome.copy())

            while len(population) < pop_size:
                chromosome = []
                for pid in bar_pids:
                    chromosome.append(random.uniform(bar_min, bar_max))
                for pid in skin_pids:
                    chromosome.append(random.uniform(skin_min, skin_max))
                population.append(chromosome)

            for gen in range(n_generations):
                if not self.is_running:
                    break

                self.log(f"\n{'='*50}")
                self.log(f"GENERATION {gen+1}/{n_generations}")
                self.log(f"{'='*50}")

                progress = 20 + (gen / n_generations) * 80
                self.update_progress(progress, f"Gen {gen+1}/{n_generations}")

                # Evaluate all individuals using SURROGATE
                fitness_scores = []
                surrogate_predictions = []

                for idx, chromosome in enumerate(population):
                    # Surrogate prediction using weighted k-nearest neighbors
                    pred_rf, pred_weight, confidence = self._surrogate_predict(
                        chromosome, X_train, y_rf_train, y_weight_train,
                        bar_min, bar_max, skin_min, skin_max, n_bars
                    )

                    # Calculate predicted fitness
                    if pred_rf >= target_rf - rf_tol:
                        pred_fitness = 1000.0 / (pred_weight + 0.001)
                    else:
                        penalty = (target_rf - pred_rf) * 100
                        pred_fitness = 1000.0 / (pred_weight + 0.001) - penalty

                    fitness_scores.append(pred_fitness)
                    surrogate_predictions.append({
                        'chromosome': chromosome,
                        'pred_rf': pred_rf,
                        'pred_weight': pred_weight,
                        'pred_fitness': pred_fitness,
                        'confidence': confidence
                    })

                # Select top candidates for actual Nastran evaluation
                # Criteria: high predicted fitness OR low confidence (exploration)
                sorted_by_fitness = sorted(surrogate_predictions, key=lambda x: x['pred_fitness'], reverse=True)
                sorted_by_uncertainty = sorted(surrogate_predictions, key=lambda x: x['confidence'])

                candidates_for_nastran = []
                # Top performers (exploitation)
                for item in sorted_by_fitness[:nastran_per_gen // 2]:
                    if item['chromosome'] not in [c['chromosome'] for c in candidates_for_nastran]:
                        candidates_for_nastran.append(item)
                # Most uncertain (exploration)
                for item in sorted_by_uncertainty[:nastran_per_gen // 2 + 1]:
                    if item['chromosome'] not in [c['chromosome'] for c in candidates_for_nastran]:
                        candidates_for_nastran.append(item)

                candidates_for_nastran = candidates_for_nastran[:nastran_per_gen]

                # Run Nastran for selected candidates
                self.log(f"\n  Running Nastran for {len(candidates_for_nastran)} candidates...")

                for cand in candidates_for_nastran:
                    if not self.is_running:
                        break

                    chromosome = cand['chromosome']
                    nastran_count += 1

                    # Set thicknesses
                    for i, pid in enumerate(bar_pids):
                        self.current_bar_thicknesses[pid] = chromosome[i]
                    for i, pid in enumerate(skin_pids):
                        self.current_skin_thicknesses[pid] = chromosome[n_bars + i]

                    # Run Nastran
                    iter_folder = os.path.join(base_folder, f"gen_{gen+1:03d}_eval_{nastran_count:03d}")
                    os.makedirs(iter_folder, exist_ok=True)
                    result = self._run_iteration(iter_folder, nastran_count, target_rf)

                    if result:
                        min_rf = result['min_rf']
                        weight = result['weight']

                        # Update surrogate training data
                        X_train.append(chromosome)
                        y_rf_train.append(min_rf)
                        y_weight_train.append(weight)

                        # Calculate actual fitness
                        if min_rf >= target_rf - rf_tol:
                            actual_fitness = 1000.0 / (weight + 0.001)
                        else:
                            penalty = (target_rf - min_rf) * 100
                            actual_fitness = 1000.0 / (weight + 0.001) - penalty

                        pred_rf = cand['pred_rf']
                        self.log(f"    Nastran #{nastran_count}: Pred RF={pred_rf:.3f} → Actual RF={min_rf:.4f}, Weight={weight:.6f}t")

                        # Update best
                        if actual_fitness > best_fitness:
                            best_fitness = actual_fitness
                            best_chromosome = chromosome.copy()
                            best_result = result
                            self.best_solution = result
                            self.log(f"    *** NEW BEST! ***")

                        # Update fitness score in population
                        for i, p in enumerate(population):
                            if p == chromosome:
                                fitness_scores[i] = actual_fitness
                                break

                # Selection and reproduction
                def tournament_select(pop, fit, k=3):
                    indices = random.sample(range(len(pop)), min(k, len(pop)))
                    best_idx = max(indices, key=lambda i: fit[i])
                    return pop[best_idx]

                new_population = []
                if best_chromosome:
                    new_population.append(best_chromosome.copy())

                while len(new_population) < pop_size:
                    parent1 = tournament_select(population, fitness_scores)
                    parent2 = tournament_select(population, fitness_scores)

                    # BLX-α crossover
                    if random.random() < crossover_rate:
                        child = []
                        alpha = 0.5
                        for i, (g1, g2) in enumerate(zip(parent1, parent2)):
                            d = abs(g2 - g1)
                            if i < n_bars:
                                low = max(bar_min, min(g1, g2) - alpha * d)
                                high = min(bar_max, max(g1, g2) + alpha * d)
                            else:
                                low = max(skin_min, min(g1, g2) - alpha * d)
                                high = min(skin_max, max(g1, g2) + alpha * d)
                            child.append(random.uniform(low, high))
                    else:
                        child = parent1.copy()

                    # Gaussian mutation
                    for i in range(len(child)):
                        if random.random() < mutation_rate:
                            if i < n_bars:
                                sigma = (bar_max - bar_min) * 0.1
                                child[i] = max(bar_min, min(bar_max, child[i] + random.gauss(0, sigma)))
                            else:
                                sigma = (skin_max - skin_min) * 0.1
                                child[i] = max(skin_min, min(skin_max, child[i] + random.gauss(0, sigma)))

                    new_population.append(child)

                population = new_population[:pop_size]

                # Log generation summary
                self.log(f"\n  Gen {gen+1}: Best Fitness={best_fitness:.2f}, Surrogate samples={len(X_train)}")

            # ========== Final Results ==========
            self.log("\n" + "="*70)
            self.log("SURROGATE-ASSISTED GA COMPLETE")
            self.log("="*70)
            self.log(f"Total Nastran evaluations: {nastran_count}")
            self.log(f"Surrogate model size: {len(X_train)} samples")

            if best_result:
                for i, pid in enumerate(bar_pids):
                    self.current_bar_thicknesses[pid] = best_chromosome[i]
                for i, pid in enumerate(skin_pids):
                    self.current_skin_thicknesses[pid] = best_chromosome[n_bars + i]

                self.log(f"\nBest Solution:")
                self.log(f"  Min RF: {best_result['min_rf']:.4f}")
                self.log(f"  Weight: {best_result['weight']:.6f}t")
                self.log(f"  Failures: {best_result['n_fail']}")

                self._update_ui()
                self._save_results(base_folder)

                # Save surrogate training data
                surrogate_data = []
                for i in range(len(X_train)):
                    row = {'RF': y_rf_train[i], 'Weight': y_weight_train[i]}
                    for j, pid in enumerate(bar_pids):
                        row[f'Bar_{pid}'] = X_train[i][j]
                    for j, pid in enumerate(skin_pids):
                        row[f'Skin_{pid}'] = X_train[i][n_bars + j]
                    surrogate_data.append(row)
                pd.DataFrame(surrogate_data).to_csv(os.path.join(base_folder, "surrogate_data.csv"), index=False)
                self.log(f"\nSurrogate training data saved to surrogate_data.csv")

                self._generate_final_report(base_folder, "Surrogate-Assisted GA", nastran_count=nastran_count,
                    extra_info={
                        "Initial Samples": initial_samples,
                        "Nastran per Generation": nastran_per_gen,
                        "Surrogate Model Size": len(X_train),
                        "Savings vs Full GA": f"{(1 - nastran_count/(pop_size*n_generations))*100:.1f}%"
                    })

                self.root.after(0, lambda: messagebox.showinfo(
                    "Surrogate-Assisted GA Complete",
                    f"Optimization finished!\n\nNastran evaluations: {nastran_count}\nWeight: {best_result['weight']:.6f}t\nMin RF: {best_result['min_rf']:.4f}"
                ))
            else:
                self.log("ERROR: No valid solution found!")

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())

        finally:
            self.is_running = False
            self.root.after(0, lambda: [self.btn_start.config(state=tk.NORMAL), self.btn_stop.config(state=tk.DISABLED)])

    def _surrogate_predict(self, chromosome, X_train, y_rf_train, y_weight_train,
                           bar_min, bar_max, skin_min, skin_max, n_bars):
        """Predict RF and Weight using weighted k-nearest neighbors (RBF-like)."""
        if len(X_train) == 0:
            return 0.5, 1.0, 0.0  # Default prediction, low confidence

        # Normalize chromosome
        def normalize(chrom):
            norm = []
            for i, val in enumerate(chrom):
                if i < n_bars:
                    norm.append((val - bar_min) / (bar_max - bar_min + 1e-10))
                else:
                    norm.append((val - skin_min) / (skin_max - skin_min + 1e-10))
            return norm

        norm_query = normalize(chromosome)

        # Calculate distances to all training points
        distances = []
        for i, x in enumerate(X_train):
            norm_x = normalize(x)
            dist = sum((a - b) ** 2 for a, b in zip(norm_query, norm_x)) ** 0.5
            distances.append((dist, i))

        # Sort by distance and take k nearest
        k = min(5, len(X_train))
        distances.sort(key=lambda x: x[0])
        nearest = distances[:k]

        # Weighted average (inverse distance weighting)
        epsilon = 1e-6
        total_weight = 0
        pred_rf = 0
        pred_wt = 0

        for dist, idx in nearest:
            w = 1.0 / (dist + epsilon)
            total_weight += w
            pred_rf += w * y_rf_train[idx]
            pred_wt += w * y_weight_train[idx]

        pred_rf /= total_weight
        pred_wt /= total_weight

        # Confidence based on average distance to nearest neighbors
        avg_dist = sum(d for d, _ in nearest) / k
        confidence = 1.0 / (1.0 + avg_dist * 10)  # Higher distance = lower confidence

        return pred_rf, pred_wt, confidence

    def _run_rsm_sqp(self):
        """Algorithm 6: RSM + SQP - Response Surface Methodology with Sequential Quadratic Programming."""
        try:
            self.log("\n" + "="*70)
            self.log("ALGORITHM: RSM + SQP")
            self.log("(Response Surface Methodology + Sequential Quadratic Programming)")
            self.log("="*70)

            # Parameters
            bar_min = float(self.bar_min_thickness.get())
            bar_max = float(self.bar_max_thickness.get())
            skin_min = float(self.skin_min_thickness.get())
            skin_max = float(self.skin_max_thickness.get())
            target_rf = float(self.target_rf.get())
            rf_tol = float(self.rf_tolerance.get())
            max_iter = int(self.max_iterations.get())

            bar_pids = list(self.bar_properties.keys())
            skin_pids = list(self.skin_properties.keys())
            n_bars = len(bar_pids)
            n_skins = len(skin_pids)
            n_vars = n_bars + n_skins

            if n_vars == 0:
                self.log("ERROR: No properties to optimize!")
                return

            self.log(f"\nVariables: {n_bars} bars + {n_skins} skins = {n_vars} total")
            self.log(f"Target RF: {target_rf}")

            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            base_folder = os.path.join(self.output_folder.get(), f"rsm_sqp_{timestamp}")
            os.makedirs(base_folder, exist_ok=True)

            # Bounds for each variable
            bounds_low = [bar_min] * n_bars + [skin_min] * n_skins
            bounds_high = [bar_max] * n_bars + [skin_max] * n_skins

            # ========== PHASE 1: DOE - Latin Hypercube Sampling ==========
            self.log("\n" + "="*50)
            self.log("PHASE 1: Design of Experiments (Latin Hypercube)")
            self.log("="*50)

            # Number of initial samples: need at least n_vars + 1 for RSM fitting
            # Use 2*n_vars + 1 as rule of thumb for good fit
            n_samples = max(n_vars + 5, 2 * n_vars + 1, 20)

            # Cap to reasonable number to avoid too many Nastran runs
            max_doe_samples = 150
            if n_samples > max_doe_samples:
                self.log(f"WARNING: Large number of variables ({n_vars}). Limiting DOE to {max_doe_samples} samples.")
                self.log(f"         Consider using Surrogate-Assisted GA for problems with many variables.")
                n_samples = max_doe_samples

            self.log(f"Generating {n_samples} DOE samples for {n_vars} variables...")

            # Latin Hypercube Sampling
            doe_samples = self._latin_hypercube_sampling(n_samples, n_vars, bounds_low, bounds_high)

            # Evaluate DOE samples with Nastran
            X_data = []  # Design points
            y_rf_data = []  # RF responses
            y_weight_data = []  # Weight responses
            nastran_count = 0

            best_result = None
            best_fitness = float('-inf')

            for idx, sample in enumerate(doe_samples):
                if not self.is_running:
                    break

                nastran_count += 1
                self.log(f"\n  DOE Sample {idx+1}/{n_samples} (Nastran #{nastran_count})")
                self.update_progress((idx/n_samples)*30, f"DOE {idx+1}/{n_samples}")

                # Set thicknesses
                for i, pid in enumerate(bar_pids):
                    self.current_bar_thicknesses[pid] = sample[i]
                for i, pid in enumerate(skin_pids):
                    self.current_skin_thicknesses[pid] = sample[n_bars + i]

                # Run Nastran
                iter_folder = os.path.join(base_folder, f"doe_{idx+1:03d}")
                os.makedirs(iter_folder, exist_ok=True)
                result = self._run_iteration(iter_folder, nastran_count, target_rf)

                if result:
                    X_data.append(sample)
                    y_rf_data.append(result['min_rf'])
                    y_weight_data.append(result['weight'])

                    self.log(f"    RF={result['min_rf']:.4f}, Weight={result['weight']:.6f}t")

                    # Track best feasible solution
                    if result['min_rf'] >= target_rf - rf_tol:
                        fitness = 1000.0 / (result['weight'] + 0.001)
                        if fitness > best_fitness:
                            best_fitness = fitness
                            best_result = result
                            self.best_solution = result
                            self.log(f"    *** FEASIBLE SOLUTION ***")

            if len(X_data) < n_vars + 1:
                self.log(f"ERROR: Not enough valid DOE samples!")
                self.log(f"       Valid samples: {len(X_data)}, Required: {n_vars + 1} (n_vars + 1)")
                self.log(f"       Most Nastran runs may have failed. Check BDF file and solver settings.")
                self.log(f"       Alternatively, try Surrogate-Assisted GA algorithm instead.")
                return

            X_data = np.array(X_data)
            y_rf_data = np.array(y_rf_data)
            y_weight_data = np.array(y_weight_data)

            self.log(f"\n  DOE Complete: {len(X_data)} valid samples")

            # ========== PHASE 2: Fit RSM Models ==========
            self.log("\n" + "="*50)
            self.log("PHASE 2: Fitting Response Surface Models")
            self.log("="*50)

            # Fit quadratic RSM for RF and Weight
            rsm_rf = self._fit_rsm(X_data, y_rf_data, bounds_low, bounds_high)
            rsm_weight = self._fit_rsm(X_data, y_weight_data, bounds_low, bounds_high)

            if rsm_rf is None or rsm_weight is None:
                self.log("ERROR: RSM fitting failed!")
                return

            self.log(f"  RF Model R²: {rsm_rf['r2']:.4f}")
            self.log(f"  Weight Model R²: {rsm_weight['r2']:.4f}")

            # ========== PHASE 3: SQP Optimization Loop ==========
            self.log("\n" + "="*50)
            self.log("PHASE 3: SQP Optimization with Trust Region")
            self.log("="*50)

            # Start from best DOE point or center
            if best_result:
                x0 = list(best_result['bar_thicknesses'].values()) + list(best_result.get('skin_thicknesses', {}).values())
                if len(x0) != n_vars:
                    x0 = [(l + h) / 2 for l, h in zip(bounds_low, bounds_high)]
            else:
                x0 = [(l + h) / 2 for l, h in zip(bounds_low, bounds_high)]

            trust_radius = 1.0  # Normalized trust region radius
            min_trust_radius = 0.1
            sqp_iterations = 0
            max_sqp_iterations = max_iter

            while sqp_iterations < max_sqp_iterations and self.is_running:
                sqp_iterations += 1
                self.log(f"\n  SQP Iteration {sqp_iterations}")
                self.update_progress(30 + (sqp_iterations/max_sqp_iterations)*60, f"SQP Iter {sqp_iterations}")

                # Define objective: minimize weight subject to RF >= target
                def objective(x):
                    return self._rsm_predict(x, rsm_weight, bounds_low, bounds_high)

                def rf_constraint(x):
                    return self._rsm_predict(x, rsm_rf, bounds_low, bounds_high) - target_rf

                # Bounds with trust region
                tr_bounds = []
                for i in range(n_vars):
                    x_norm = (x0[i] - bounds_low[i]) / (bounds_high[i] - bounds_low[i])
                    range_i = bounds_high[i] - bounds_low[i]
                    tr_low = max(bounds_low[i], x0[i] - trust_radius * range_i)
                    tr_high = min(bounds_high[i], x0[i] + trust_radius * range_i)
                    tr_bounds.append((tr_low, tr_high))

                # SQP optimization
                constraints = {'type': 'ineq', 'fun': rf_constraint}

                try:
                    result_sqp = minimize(
                        objective, x0,
                        method='SLSQP',
                        bounds=tr_bounds,
                        constraints=constraints,
                        options={'maxiter': 100, 'ftol': 1e-6}
                    )
                    x_opt = result_sqp.x
                    pred_weight = result_sqp.fun
                    pred_rf = self._rsm_predict(x_opt, rsm_rf, bounds_low, bounds_high)

                    self.log(f"    SQP Result: Pred RF={pred_rf:.4f}, Pred Weight={pred_weight:.6f}")

                except Exception as e:
                    self.log(f"    SQP failed: {e}")
                    break

                # Validate with Nastran
                nastran_count += 1
                self.log(f"    Validating with Nastran #{nastran_count}...")

                for i, pid in enumerate(bar_pids):
                    self.current_bar_thicknesses[pid] = float(x_opt[i])
                for i, pid in enumerate(skin_pids):
                    self.current_skin_thicknesses[pid] = float(x_opt[n_bars + i])

                iter_folder = os.path.join(base_folder, f"sqp_{sqp_iterations:03d}")
                os.makedirs(iter_folder, exist_ok=True)
                result = self._run_iteration(iter_folder, nastran_count, target_rf)

                if result:
                    actual_rf = result['min_rf']
                    actual_weight = result['weight']

                    self.log(f"    Actual: RF={actual_rf:.4f}, Weight={actual_weight:.6f}t")

                    # Calculate prediction error
                    rf_error = abs(pred_rf - actual_rf) / max(actual_rf, 0.001)
                    weight_error = abs(pred_weight - actual_weight) / max(actual_weight, 0.001)

                    self.log(f"    Errors: RF={rf_error*100:.1f}%, Weight={weight_error*100:.1f}%")

                    # Update training data
                    X_data = np.vstack([X_data, x_opt])
                    y_rf_data = np.append(y_rf_data, actual_rf)
                    y_weight_data = np.append(y_weight_data, actual_weight)

                    # Check if solution is feasible
                    if actual_rf >= target_rf - rf_tol:
                        fitness = 1000.0 / (actual_weight + 0.001)
                        if fitness > best_fitness:
                            best_fitness = fitness
                            best_result = result
                            self.best_solution = result
                            self.log(f"    *** NEW BEST! ***")

                    # Trust region update
                    if rf_error < 0.1 and weight_error < 0.1:
                        # Good prediction, expand trust region
                        trust_radius = min(trust_radius * 1.5, 1.0)
                        x0 = list(x_opt)
                        self.log(f"    Trust region expanded: {trust_radius:.2f}")
                    elif rf_error > 0.3 or weight_error > 0.3:
                        # Poor prediction, shrink trust region and refit RSM
                        trust_radius = max(trust_radius * 0.5, min_trust_radius)
                        self.log(f"    Trust region shrunk: {trust_radius:.2f}")

                        # Refit RSM with new data
                        rsm_rf = self._fit_rsm(X_data, y_rf_data, bounds_low, bounds_high)
                        rsm_weight = self._fit_rsm(X_data, y_weight_data, bounds_low, bounds_high)
                        self.log(f"    RSM refitted: RF R²={rsm_rf['r2']:.4f}, Weight R²={rsm_weight['r2']:.4f}")
                    else:
                        # Acceptable prediction
                        x0 = list(x_opt)
                        # Refit RSM periodically
                        if sqp_iterations % 3 == 0:
                            rsm_rf = self._fit_rsm(X_data, y_rf_data, bounds_low, bounds_high)
                            rsm_weight = self._fit_rsm(X_data, y_weight_data, bounds_low, bounds_high)

                    # Check convergence
                    if trust_radius <= min_trust_radius and rf_error < 0.05:
                        self.log(f"\n  CONVERGED at iteration {sqp_iterations}")
                        break

                else:
                    self.log(f"    Nastran failed!")
                    trust_radius = max(trust_radius * 0.5, min_trust_radius)

            # ========== Final Results ==========
            self.log("\n" + "="*70)
            self.log("RSM + SQP OPTIMIZATION COMPLETE")
            self.log("="*70)
            self.log(f"Total Nastran evaluations: {nastran_count}")
            self.log(f"DOE samples: {n_samples}")
            self.log(f"SQP iterations: {sqp_iterations}")

            if best_result:
                for i, pid in enumerate(bar_pids):
                    self.current_bar_thicknesses[pid] = best_result['bar_thicknesses'].get(pid, bar_min)
                for i, pid in enumerate(skin_pids):
                    self.current_skin_thicknesses[pid] = best_result.get('skin_thicknesses', {}).get(pid, skin_min)

                self.log(f"\nBest Solution:")
                self.log(f"  Min RF: {best_result['min_rf']:.4f}")
                self.log(f"  Weight: {best_result['weight']:.6f}t")
                self.log(f"  Failures: {best_result['n_fail']}")

                self._update_ui()
                self._save_results(base_folder)
                self._generate_final_report(base_folder, "RSM + SQP", nastran_count=nastran_count,
                    extra_info={
                        "DOE Samples": n_samples,
                        "SQP Iterations": sqp_iterations,
                        "Final RF Model R²": f"{rsm_rf['r2']:.4f}",
                        "Final Weight Model R²": f"{rsm_weight['r2']:.4f}",
                        "RSM Model Size": len(X_data)
                    })

                # Save RSM data
                rsm_data = []
                for i in range(len(X_data)):
                    row = {'RF': y_rf_data[i], 'Weight': y_weight_data[i]}
                    for j, pid in enumerate(bar_pids):
                        row[f'Bar_{pid}'] = X_data[i][j]
                    for j, pid in enumerate(skin_pids):
                        row[f'Skin_{pid}'] = X_data[i][n_bars + j]
                    rsm_data.append(row)
                pd.DataFrame(rsm_data).to_csv(os.path.join(base_folder, "rsm_training_data.csv"), index=False)

                self.root.after(0, lambda: messagebox.showinfo(
                    "RSM + SQP Complete",
                    f"Optimization finished!\n\nNastran evaluations: {nastran_count}\nWeight: {best_result['weight']:.6f}t\nMin RF: {best_result['min_rf']:.4f}"
                ))
            else:
                self.log("ERROR: No feasible solution found!")

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())

        finally:
            self.is_running = False
            self.root.after(0, lambda: [self.btn_start.config(state=tk.NORMAL), self.btn_stop.config(state=tk.DISABLED)])

    def _run_topdown_algorithm(self):
        """Algorithm 7: Top-Down - Start from max thickness, reduce until RF reaches target.

        This is a Fully Stressed Design (FSD) approach:
        1. Start with maximum thicknesses (structure is over-designed, RF >> target)
        2. Reduce thicknesses proportionally based on RF margin
        3. Stop when RF approaches target (optimal weight)

        Advantages:
        - Always starts from feasible region (no failures initially)
        - Converges to minimum weight with RF ≈ target
        - Simple and robust
        """
        try:
            self.log("\n" + "="*70)
            self.log("ALGORITHM: TOP-DOWN (MAX TO TARGET)")
            self.log("="*70)
            self.log("Strategy: Start overdesigned, reduce until RF = target")
            self.log("="*70)

            max_iter = int(self.max_iterations.get())
            target_rf = float(self.target_rf.get())
            rf_tol = float(self.rf_tolerance.get())
            bar_min = float(self.bar_min_thickness.get())
            bar_max = float(self.bar_max_thickness.get())
            skin_min = float(self.skin_min_thickness.get())
            skin_max = float(self.skin_max_thickness.get())
            step = float(self.thickness_step.get())

            # Calculate bar-skin proximity mapping
            self.calculate_bar_skin_proximity()

            # Create output folder
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            base_folder = os.path.join(self.output_folder.get(), f"topdown_{timestamp}")
            os.makedirs(base_folder, exist_ok=True)

            # ========== PHASE 1: Initialize thicknesses ==========
            self.log("\n" + "="*50)
            self.log("PHASE 1: Initialize thicknesses")
            self.log("="*50)

            # Bar properties: ALL start at MAXIMUM
            for pid in self.bar_properties:
                self.current_bar_thicknesses[pid] = bar_max

            # Skin properties: Related (near bars) → MAX, Unrelated → MIN
            # Find all skin PIDs that are related to any bar
            related_skins = set()
            for bar_pid, nearby_skins in self.bar_to_nearby_skins.items():
                related_skins.update(nearby_skins)

            related_count = 0
            unrelated_count = 0
            for pid in self.skin_properties:
                if pid in related_skins:
                    # Related to bars - start at MAX (will be optimized)
                    self.current_skin_thicknesses[pid] = skin_max
                    related_count += 1
                else:
                    # Not related to any bar - start at MIN (save weight)
                    self.current_skin_thicknesses[pid] = skin_min
                    unrelated_count += 1

            self.log(f"  Bar thicknesses: {len(self.bar_properties)} properties → MAX ({bar_max})")
            self.log(f"  Skin thicknesses:")
            self.log(f"    Related (near bars): {related_count} properties → MAX ({skin_max})")
            self.log(f"    Unrelated (far): {unrelated_count} properties → MIN ({skin_min})")

            # ========== PHASE 2: Iterative Lightening ==========
            self.log("\n" + "="*50)
            self.log("PHASE 2: Iterative Lightening")
            self.log("="*50)

            best_weight = float('inf')
            converged = False
            no_improvement_count = 0
            max_no_improvement = 5

            for iteration in range(1, max_iter + 1):
                if not self.is_running:
                    break

                self.log(f"\n{'='*50}")
                self.log(f"ITERATION {iteration}/{max_iter}")
                self.log(f"{'='*50}")

                iter_folder = os.path.join(base_folder, f"iter_{iteration:03d}")
                os.makedirs(iter_folder, exist_ok=True)

                self.update_progress((iteration/max_iter)*100, f"Iter {iteration}/{max_iter}")

                # Run Nastran and get RF
                result = self._run_iteration(iter_folder, iteration, target_rf)

                if not result:
                    self.log("  ERROR: Iteration failed!")
                    continue

                self.iteration_results.append(result)
                min_rf = result['min_rf']
                weight = result['weight']
                n_fail = result['n_fail']

                self.log(f"\n  Summary: Min RF={min_rf:.4f}, Fails={n_fail}, Weight={weight:.6f}t")

                # Calculate per-property RF statistics
                rf_details = result.get('rf_details', [])
                pid_min_rf = {}
                for d in rf_details:
                    pid = d.get('pid')
                    rf = d.get('rf', 0)
                    if pid:
                        if pid not in pid_min_rf or rf < pid_min_rf[pid]:
                            pid_min_rf[pid] = rf

                # Count how many properties are converged (RF within tolerance)
                n_converged = 0
                n_total = 0
                for pid, rf in pid_min_rf.items():
                    n_total += 1
                    if target_rf - rf_tol <= rf <= target_rf + rf_tol:
                        n_converged += 1

                convergence_pct = (n_converged / n_total * 100) if n_total > 0 else 0
                self.log(f"  Per-Property Convergence: {n_converged}/{n_total} ({convergence_pct:.1f}%) properties at RF≈{target_rf}")

                # Check convergence: ALL properties should be within tolerance
                if n_total > 0 and n_converged == n_total:
                    self.log(f"\n  *** FULLY CONVERGED! All {n_total} properties have RF≈{target_rf} ***")
                    converged = True
                    if weight < best_weight:
                        best_weight = weight
                        self.best_solution = result
                    break

                # Track best feasible solution (min RF >= target)
                if min_rf >= target_rf - rf_tol and weight < best_weight:
                    best_weight = weight
                    self.best_solution = result
                    self.log(f"  *** NEW BEST: Weight={weight:.6f}t ***")
                    no_improvement_count = 0
                else:
                    no_improvement_count += 1

                # Check if stuck
                if no_improvement_count >= max_no_improvement:
                    self.log(f"\n  No improvement for {max_no_improvement} iterations.")

                # ========== FULLY STRESSED DESIGN: Per-Property Update ==========
                # Each property is updated based on its OWN RF, not global min RF
                # Goal: Make ALL properties have RF ≈ target (1.0)

                self.log(f"\n  Applying Fully Stressed Design (per-property)...")

                # pid_min_rf already calculated above

                # Stress ratio exponent (alpha < 1 for stability)
                alpha = 0.5  # Higher value = faster convergence but less stable

                # Track changes
                increased_count = 0
                decreased_count = 0
                unchanged_count = 0

                # Update BAR thicknesses - each property independently
                for pid in self.bar_properties:
                    old_t = self.current_bar_thicknesses[pid]
                    prop_rf = pid_min_rf.get(pid, None)

                    if prop_rf is None:
                        # No RF data for this property, skip
                        unchanged_count += 1
                        continue

                    # Stress Ratio Method: new_t = old_t * (target_rf / actual_rf)^alpha
                    if prop_rf > target_rf + rf_tol:
                        # Over-designed: REDUCE thickness
                        ratio = (target_rf / prop_rf) ** alpha
                        ratio = max(ratio, 0.7)  # Max 30% reduction per iteration
                        new_t = old_t * ratio
                        decreased_count += 1
                    elif prop_rf < target_rf - rf_tol:
                        # Under-designed: INCREASE thickness
                        ratio = (target_rf / prop_rf) ** alpha
                        ratio = min(ratio, 1.3)  # Max 30% increase per iteration
                        new_t = old_t * ratio
                        increased_count += 1
                    else:
                        # Within tolerance, keep it
                        new_t = old_t
                        unchanged_count += 1

                    new_t = max(bar_min, min(bar_max, new_t))
                    self.current_bar_thicknesses[pid] = new_t

                # Update SKIN thicknesses - PROXIMITY-BASED (coupled optimization)
                # Each skin is updated based on the RF of NEARBY bars (within search distance)
                # Skin doesn't have its own allowable, but affects bar stress

                skin_decreased = 0
                skin_increased = 0
                skin_unchanged = 0

                # Build: skin_pid -> controlling bar RF (min RF of nearby bars)
                skin_controlling_rf = {}
                for bar_pid, nearby_skins in self.bar_to_nearby_skins.items():
                    bar_rf = pid_min_rf.get(bar_pid, None)
                    if bar_rf is None:
                        continue
                    for skin_pid in nearby_skins:
                        if skin_pid not in skin_controlling_rf or bar_rf < skin_controlling_rf[skin_pid]:
                            skin_controlling_rf[skin_pid] = bar_rf

                for skin_pid in self.skin_properties:
                    old_t = self.current_skin_thicknesses[skin_pid]

                    # Use the controlling bar RF for this skin (min RF of nearby bars)
                    controlling_rf = skin_controlling_rf.get(skin_pid, None)

                    if controlling_rf is None:
                        # No nearby bars - skin is not coupled, keep unchanged
                        skin_unchanged += 1
                        new_t = old_t
                    elif controlling_rf > target_rf + rf_tol:
                        # Nearby bars are over-designed: REDUCE skin thickness
                        skin_ratio = (target_rf / controlling_rf) ** (alpha * 0.7)
                        skin_ratio = max(skin_ratio, 0.85)  # Max 15% reduction
                        new_t = old_t * skin_ratio
                        skin_decreased += 1
                    elif controlling_rf < target_rf - rf_tol:
                        # Nearby bars are under-designed: INCREASE skin thickness
                        skin_ratio = (target_rf / controlling_rf) ** (alpha * 0.7)
                        skin_ratio = min(skin_ratio, 1.15)  # Max 15% increase
                        new_t = old_t * skin_ratio
                        skin_increased += 1
                    else:
                        # Within tolerance
                        new_t = old_t
                        skin_unchanged += 1

                    new_t = max(skin_min, min(skin_max, new_t))
                    self.current_skin_thicknesses[skin_pid] = new_t

                self.log(f"    Bar properties: {increased_count} increased, {decreased_count} decreased, {unchanged_count} unchanged")
                self.log(f"    Skin properties: {skin_increased} increased, {skin_decreased} decreased, {skin_unchanged} unchanged")
                self.log(f"    (Skin updated based on nearby bar RF - {len(skin_controlling_rf)} skins coupled)")

            # ========== FINAL RESULTS ==========
            self.log("\n" + "="*70)
            self.log("TOP-DOWN OPTIMIZATION COMPLETE")
            self.log("="*70)

            if self.best_solution:
                self.log(f"\nBest Solution:")
                self.log(f"  Min RF: {self.best_solution['min_rf']:.4f}")
                self.log(f"  Weight: {self.best_solution['weight']:.6f} tonnes")
                self.log(f"  Found at iteration: {self.best_solution['iteration']}")
                self.log(f"  Converged: {'Yes' if converged else 'No'}")

                self._generate_final_report(base_folder, "Top-Down (Max to Target)",
                    nastran_count=iteration,
                    extra_info={
                        "Strategy": "Fully Stressed Design",
                        "Start": "Maximum thicknesses",
                        "Converged": "Yes" if converged else "No",
                        "Final Iterations": iteration
                    })

                self.root.after(0, lambda: self.result_summary.config(
                    text=f"Best: Weight={self.best_solution['weight']:.6f}t, RF={self.best_solution['min_rf']:.4f}",
                    foreground="green"
                ))

                self.root.after(0, lambda: messagebox.showinfo(
                    "Top-Down Complete",
                    f"Optimization Complete!\n\n"
                    f"Best RF: {self.best_solution['min_rf']:.4f}\n"
                    f"Best Weight: {self.best_solution['weight']:.6f} tonnes\n"
                    f"Iterations: {iteration}\n"
                    f"Converged: {'Yes' if converged else 'No'}"
                ))
            else:
                self.log("ERROR: No feasible solution found!")

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())

        finally:
            self.is_running = False
            self.root.after(0, lambda: [self.btn_start.config(state=tk.NORMAL), self.btn_stop.config(state=tk.DISABLED)])

    def _run_bottomup_algorithm(self):
        """Algorithm 8: Bottom-Up - Start from min thickness, increase until RF reaches target.

        This is an inverse Fully Stressed Design (FSD) approach:
        1. Start with minimum thicknesses (structure is under-designed, RF << target)
        2. Increase thicknesses proportionally based on RF deficit
        3. Stop when RF approaches target (optimal weight)

        Advantages:
        - Always starts from lightest possible design
        - Builds up only where needed
        - Converges to minimum weight with RF ≈ target
        """
        try:
            self.log("\n" + "="*70)
            self.log("ALGORITHM: BOTTOM-UP (MIN TO TARGET)")
            self.log("="*70)
            self.log("Strategy: Start underdesigned, increase until RF = target")
            self.log("="*70)

            max_iter = int(self.max_iterations.get())
            target_rf = float(self.target_rf.get())
            rf_tol = float(self.rf_tolerance.get())
            bar_min = float(self.bar_min_thickness.get())
            bar_max = float(self.bar_max_thickness.get())
            skin_min = float(self.skin_min_thickness.get())
            skin_max = float(self.skin_max_thickness.get())
            step = float(self.thickness_step.get())

            # Calculate bar-skin proximity mapping
            self.calculate_bar_skin_proximity()

            # Create output folder
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            base_folder = os.path.join(self.output_folder.get(), f"bottomup_{timestamp}")
            os.makedirs(base_folder, exist_ok=True)

            # ========== PHASE 1: Initialize thicknesses ==========
            self.log("\n" + "="*50)
            self.log("PHASE 1: Initialize thicknesses at MINIMUM")
            self.log("="*50)

            # Bar properties: ALL start at MINIMUM
            for pid in self.bar_properties:
                self.current_bar_thicknesses[pid] = bar_min

            # Skin properties: Related (near bars) → MIN, Unrelated → MIN
            # Both start at MIN, but related skins will be optimized with bars
            related_skins = set()
            for bar_pid, nearby_skins in self.bar_to_nearby_skins.items():
                related_skins.update(nearby_skins)

            related_count = 0
            unrelated_count = 0
            for pid in self.skin_properties:
                if pid in related_skins:
                    self.current_skin_thicknesses[pid] = skin_min
                    related_count += 1
                else:
                    self.current_skin_thicknesses[pid] = skin_min
                    unrelated_count += 1

            self.log(f"  Bar thicknesses: {len(self.bar_properties)} properties → MIN ({bar_min})")
            self.log(f"  Skin thicknesses:")
            self.log(f"    Related (near bars): {related_count} properties → MIN ({skin_min})")
            self.log(f"    Unrelated (far): {unrelated_count} properties → MIN ({skin_min})")

            # ========== PHASE 2: Iterative Strengthening ==========
            self.log("\n" + "="*50)
            self.log("PHASE 2: Iterative Strengthening")
            self.log("="*50)

            best_weight = float('inf')
            converged = False
            no_improvement_count = 0
            max_no_improvement = 5

            for iteration in range(1, max_iter + 1):
                if not self.is_running:
                    break

                self.log(f"\n{'='*50}")
                self.log(f"ITERATION {iteration}/{max_iter}")
                self.log(f"{'='*50}")

                iter_folder = os.path.join(base_folder, f"iter_{iteration:03d}")
                os.makedirs(iter_folder, exist_ok=True)

                self.update_progress((iteration/max_iter)*100, f"Iter {iteration}/{max_iter}")

                # Run Nastran and get RF
                result = self._run_iteration(iter_folder, iteration, target_rf)

                if not result:
                    self.log("  ERROR: Iteration failed!")
                    continue

                self.iteration_results.append(result)
                min_rf = result['min_rf']
                weight = result['weight']
                n_fail = result['n_fail']

                self.log(f"\n  Summary: Min RF={min_rf:.4f}, Fails={n_fail}, Weight={weight:.6f}t")

                # Calculate per-property RF statistics
                rf_details = result.get('rf_details', [])
                pid_min_rf = {}
                for d in rf_details:
                    pid = d.get('pid')
                    rf = d.get('rf', 0)
                    if pid:
                        if pid not in pid_min_rf or rf < pid_min_rf[pid]:
                            pid_min_rf[pid] = rf

                # Count how many properties are converged (RF within tolerance)
                n_converged = 0
                n_total = 0
                for pid, rf in pid_min_rf.items():
                    n_total += 1
                    if target_rf - rf_tol <= rf <= target_rf + rf_tol:
                        n_converged += 1

                convergence_pct = (n_converged / n_total * 100) if n_total > 0 else 0
                self.log(f"  Per-Property Convergence: {n_converged}/{n_total} ({convergence_pct:.1f}%) properties at RF≈{target_rf}")

                # Check convergence: ALL properties should be within tolerance
                if n_total > 0 and n_converged == n_total:
                    self.log(f"\n  *** FULLY CONVERGED! All {n_total} properties have RF≈{target_rf} ***")
                    converged = True
                    if weight < best_weight:
                        best_weight = weight
                        self.best_solution = result
                    break

                # Track best feasible solution (min RF >= target)
                if min_rf >= target_rf - rf_tol and weight < best_weight:
                    best_weight = weight
                    self.best_solution = result
                    self.log(f"  *** NEW BEST: Weight={weight:.6f}t ***")
                    no_improvement_count = 0
                else:
                    no_improvement_count += 1

                # Check if stuck
                if no_improvement_count >= max_no_improvement:
                    self.log(f"\n  No improvement for {max_no_improvement} iterations.")

                # ========== FULLY STRESSED DESIGN: Per-Property Update ==========
                # Each property is updated based on its OWN RF, not global min RF
                # Goal: Make ALL properties have RF ≈ target (1.0)

                self.log(f"\n  Applying Fully Stressed Design (per-property, bottom-up)...")

                # Stress ratio exponent (alpha < 1 for stability)
                alpha = 0.5

                # Track changes
                increased_count = 0
                decreased_count = 0
                unchanged_count = 0

                # Update BAR thicknesses - each property independently
                for pid in self.bar_properties:
                    old_t = self.current_bar_thicknesses[pid]
                    prop_rf = pid_min_rf.get(pid, None)

                    if prop_rf is None:
                        unchanged_count += 1
                        continue

                    # Stress Ratio Method: new_t = old_t * (target_rf / actual_rf)^alpha
                    if prop_rf < target_rf - rf_tol:
                        # Under-designed: INCREASE thickness (primary direction in bottom-up)
                        ratio = (target_rf / prop_rf) ** alpha
                        ratio = min(ratio, 1.3)  # Max 30% increase per iteration
                        new_t = old_t * ratio
                        increased_count += 1
                    elif prop_rf > target_rf + rf_tol:
                        # Over-designed: REDUCE thickness
                        ratio = (target_rf / prop_rf) ** alpha
                        ratio = max(ratio, 0.7)  # Max 30% reduction per iteration
                        new_t = old_t * ratio
                        decreased_count += 1
                    else:
                        # Within tolerance, keep it
                        new_t = old_t
                        unchanged_count += 1

                    new_t = max(bar_min, min(bar_max, new_t))
                    self.current_bar_thicknesses[pid] = new_t

                # Update SKIN thicknesses - PROXIMITY-BASED (coupled optimization)
                skin_decreased = 0
                skin_increased = 0
                skin_unchanged = 0

                # Build: skin_pid -> controlling bar RF (min RF of nearby bars)
                skin_controlling_rf = {}
                for bar_pid, nearby_skins in self.bar_to_nearby_skins.items():
                    bar_rf = pid_min_rf.get(bar_pid, None)
                    if bar_rf is None:
                        continue
                    for skin_pid in nearby_skins:
                        if skin_pid not in skin_controlling_rf or bar_rf < skin_controlling_rf[skin_pid]:
                            skin_controlling_rf[skin_pid] = bar_rf

                for skin_pid in self.skin_properties:
                    old_t = self.current_skin_thicknesses[skin_pid]

                    controlling_rf = skin_controlling_rf.get(skin_pid, None)

                    if controlling_rf is None:
                        # No nearby bars - skin is not coupled, keep at MIN
                        skin_unchanged += 1
                        new_t = old_t
                    elif controlling_rf < target_rf - rf_tol:
                        # Nearby bars are under-designed: INCREASE skin thickness
                        skin_ratio = (target_rf / controlling_rf) ** (alpha * 0.7)
                        skin_ratio = min(skin_ratio, 1.15)  # Max 15% increase
                        new_t = old_t * skin_ratio
                        skin_increased += 1
                    elif controlling_rf > target_rf + rf_tol:
                        # Nearby bars are over-designed: REDUCE skin thickness
                        skin_ratio = (target_rf / controlling_rf) ** (alpha * 0.7)
                        skin_ratio = max(skin_ratio, 0.85)  # Max 15% reduction
                        new_t = old_t * skin_ratio
                        skin_decreased += 1
                    else:
                        # Within tolerance
                        new_t = old_t
                        skin_unchanged += 1

                    new_t = max(skin_min, min(skin_max, new_t))
                    self.current_skin_thicknesses[skin_pid] = new_t

                self.log(f"    Bar properties: {increased_count} increased, {decreased_count} decreased, {unchanged_count} unchanged")
                self.log(f"    Skin properties: {skin_increased} increased, {skin_decreased} decreased, {skin_unchanged} unchanged")
                self.log(f"    (Skin updated based on nearby bar RF - {len(skin_controlling_rf)} skins coupled)")

            # ========== FINAL RESULTS ==========
            self.log("\n" + "="*70)
            self.log("BOTTOM-UP OPTIMIZATION COMPLETE")
            self.log("="*70)

            if self.best_solution:
                self.log(f"\nBest Solution:")
                self.log(f"  Min RF: {self.best_solution['min_rf']:.4f}")
                self.log(f"  Weight: {self.best_solution['weight']:.6f} tonnes")
                self.log(f"  Found at iteration: {self.best_solution['iteration']}")
                self.log(f"  Converged: {'Yes' if converged else 'No'}")

                self._generate_final_report(base_folder, "Bottom-Up (Min to Target)",
                    nastran_count=iteration,
                    extra_info={
                        "Strategy": "Inverse Fully Stressed Design",
                        "Start": "Minimum thicknesses",
                        "Converged": "Yes" if converged else "No",
                        "Final Iterations": iteration
                    })

                self.root.after(0, lambda: self.result_summary.config(
                    text=f"Best: Weight={self.best_solution['weight']:.6f}t, RF={self.best_solution['min_rf']:.4f}",
                    foreground="green"
                ))

                self.root.after(0, lambda: messagebox.showinfo(
                    "Bottom-Up Complete",
                    f"Optimization Complete!\n\n"
                    f"Best RF: {self.best_solution['min_rf']:.4f}\n"
                    f"Best Weight: {self.best_solution['weight']:.6f} tonnes\n"
                    f"Iterations: {iteration}\n"
                    f"Converged: {'Yes' if converged else 'No'}"
                ))
            else:
                self.log("ERROR: No feasible solution found!")

        except Exception as e:
            self.log(f"ERROR: {e}")
            import traceback
            self.log(traceback.format_exc())

        finally:
            self.is_running = False
            self.root.after(0, lambda: [self.btn_start.config(state=tk.NORMAL), self.btn_stop.config(state=tk.DISABLED)])

    def _latin_hypercube_sampling(self, n_samples, n_vars, bounds_low, bounds_high):
        """Generate Latin Hypercube Samples."""
        samples = []

        # Create intervals for each variable
        for i in range(n_samples):
            sample = []
            for j in range(n_vars):
                # Stratified random within interval
                low = bounds_low[j] + (bounds_high[j] - bounds_low[j]) * (i / n_samples)
                high = bounds_low[j] + (bounds_high[j] - bounds_low[j]) * ((i + 1) / n_samples)
                sample.append(random.uniform(low, high))
            samples.append(sample)

        # Shuffle each column independently for better space-filling
        samples = np.array(samples)
        for j in range(n_vars):
            np.random.shuffle(samples[:, j])

        return samples.tolist()

    def _fit_rsm(self, X, y, bounds_low, bounds_high):
        """Fit a 2nd order polynomial Response Surface Model."""
        try:
            n_samples, n_vars = X.shape

            # Normalize X to [-1, 1]
            X_norm = np.zeros_like(X)
            for j in range(n_vars):
                mid = (bounds_low[j] + bounds_high[j]) / 2
                half_range = (bounds_high[j] - bounds_low[j]) / 2
                X_norm[:, j] = (X[:, j] - mid) / half_range if half_range > 0 else 0

            # Build design matrix for quadratic model
            # [1, x1, x2, ..., x1^2, x2^2, ..., x1*x2, x1*x3, ...]
            design_matrix = [np.ones(n_samples)]  # Constant term

            # Linear terms
            for j in range(n_vars):
                design_matrix.append(X_norm[:, j])

            # Quadratic terms
            for j in range(n_vars):
                design_matrix.append(X_norm[:, j] ** 2)

            # Interaction terms (limit to avoid overfitting)
            if n_vars <= 10:
                for i, j in combinations(range(n_vars), 2):
                    design_matrix.append(X_norm[:, i] * X_norm[:, j])

            A = np.column_stack(design_matrix)

            # Solve least squares
            coeffs, residuals, rank, s = np.linalg.lstsq(A, y, rcond=None)

            # Calculate R²
            y_pred = A @ coeffs
            ss_res = np.sum((y - y_pred) ** 2)
            ss_tot = np.sum((y - np.mean(y)) ** 2)
            r2 = 1 - (ss_res / ss_tot) if ss_tot > 0 else 0

            return {
                'coeffs': coeffs,
                'n_vars': n_vars,
                'bounds_low': bounds_low,
                'bounds_high': bounds_high,
                'r2': r2
            }

        except Exception as e:
            self.log(f"RSM fitting error: {e}")
            return None

    def _rsm_predict(self, x, rsm, bounds_low, bounds_high):
        """Predict using RSM model."""
        n_vars = rsm['n_vars']
        coeffs = rsm['coeffs']

        # Normalize x to [-1, 1]
        x_norm = []
        for j in range(n_vars):
            mid = (bounds_low[j] + bounds_high[j]) / 2
            half_range = (bounds_high[j] - bounds_low[j]) / 2
            x_norm.append((x[j] - mid) / half_range if half_range > 0 else 0)

        # Build feature vector
        features = [1.0]  # Constant

        # Linear
        for j in range(n_vars):
            features.append(x_norm[j])

        # Quadratic
        for j in range(n_vars):
            features.append(x_norm[j] ** 2)

        # Interactions
        if n_vars <= 10:
            for i, j in combinations(range(n_vars), 2):
                features.append(x_norm[i] * x_norm[j])

        return np.dot(features, coeffs)

    def _run_fast_ga_internal(self):
        """Internal Fast GA without UI cleanup (for Hybrid)."""
        # Parameters
        bar_min = float(self.bar_min_thickness.get())
        bar_max = float(self.bar_max_thickness.get())
        skin_min = float(self.skin_min_thickness.get())
        skin_max = float(self.skin_max_thickness.get())
        target_rf = float(self.target_rf.get())
        rf_tol = float(self.rf_tolerance.get())

        pop_size = int(self.ga_population.get())
        n_generations = int(self.ga_generations.get())
        mutation_rate = float(self.ga_mutation_rate.get())
        crossover_rate = float(self.ga_crossover_rate.get())

        bar_pids = list(self.bar_properties.keys())
        skin_pids = list(self.skin_properties.keys())
        n_bars = len(bar_pids)
        n_genes = n_bars + len(skin_pids)

        if n_genes == 0:
            return

        self._init_reference_stresses(bar_pids, skin_pids, bar_min, skin_min)

        # Initialize population
        population = []
        for _ in range(pop_size):
            chromosome = []
            for pid in bar_pids:
                chromosome.append(random.uniform(bar_min, bar_max))
            for pid in skin_pids:
                chromosome.append(random.uniform(skin_min, skin_max))
            population.append(chromosome)

        best_fitness = float('inf')
        best_chromosome = None

        for gen in range(n_generations):
            if not self.is_running:
                break

            fitness_values = []
            for chromosome in population:
                fit = self._evaluate_surrogate_fitness(
                    chromosome, bar_pids, skin_pids,
                    bar_min, bar_max, skin_min, skin_max,
                    target_rf, rf_tol
                )
                fitness_values.append(fit)

            min_fit_idx = fitness_values.index(min(fitness_values))
            if fitness_values[min_fit_idx] < best_fitness:
                best_fitness = fitness_values[min_fit_idx]
                best_chromosome = population[min_fit_idx].copy()

            if gen % 20 == 0:
                self.update_progress((gen / n_generations) * 50, f"GA Gen {gen}/{n_generations}")
                self.log(f"  Gen {gen}: Fitness = {best_fitness:.6f}")

            # Evolution
            new_population = []
            while len(new_population) < pop_size:
                idx1, idx2 = random.sample(range(pop_size), 2)
                parent1 = population[idx1] if fitness_values[idx1] < fitness_values[idx2] else population[idx2]

                idx3, idx4 = random.sample(range(pop_size), 2)
                parent2 = population[idx3] if fitness_values[idx3] < fitness_values[idx4] else population[idx4]

                if random.random() < crossover_rate:
                    child = self._blx_crossover(parent1, parent2)
                else:
                    child = parent1.copy()

                child = self._gaussian_mutation(child, mutation_rate, n_bars,
                                                bar_min, bar_max, skin_min, skin_max)
                new_population.append(child)

            population = new_population

        # Apply best solution
        if best_chromosome:
            for i, pid in enumerate(bar_pids):
                self.current_bar_thicknesses[pid] = best_chromosome[i]
            for i, pid in enumerate(skin_pids):
                self.current_skin_thicknesses[pid] = best_chromosome[n_bars + i]

            self.log(f"\nFast GA Result: Fitness = {best_fitness:.6f}")

    def _run_iteration(self, folder, iteration, target_rf):
        try:
            # Handle multiple BDFs
            n_bdfs = len(self.bdf_models) if hasattr(self, 'bdf_models') and self.bdf_models else 1
            all_stresses = []

            if n_bdfs > 1:
                self.log(f"  Processing {n_bdfs} BDF files...")

            for bdf_idx, bdf_info in enumerate(self.bdf_models if n_bdfs > 1 else [{'model': self.bdf_model, 'path': self.bdf_paths[0] if self.bdf_paths else '', 'name': 'main.bdf'}]):
                bdf_name = bdf_info['name']
                bdf_subfolder = os.path.join(folder, f"bdf_{bdf_idx+1}_{os.path.splitext(bdf_name)[0]}") if n_bdfs > 1 else folder
                os.makedirs(bdf_subfolder, exist_ok=True)

                if n_bdfs > 1:
                    self.log(f"\n  --- BDF {bdf_idx+1}/{n_bdfs}: {bdf_name} ---")

                # 1. Write BDF
                self.log("  [1] Writing BDF...")
                bdf_path = self._write_bdf_for_model(bdf_subfolder, bdf_info['model'], bdf_info['path'])

                # 2. Apply offsets
                self.log("  [2] Applying offsets...")
                offset_bdf = self._apply_offsets(bdf_path, bdf_subfolder)

                # 3. Run Nastran
                self.log("  [3] Running Nastran...")
                self._run_nastran(offset_bdf or bdf_path, bdf_subfolder)

                # 4. Extract stresses from this BDF's OP2
                self.log("  [4] Extracting stresses...")
                stresses = self._extract_stresses(bdf_subfolder)
                all_stresses.extend(stresses)

                if stresses:
                    bar_stresses = [s for s in stresses if s['type'] == 'bar']
                    shell_stresses = [s for s in stresses if s['type'] == 'shell']
                    self.log(f"    Extracted: {len(bar_stresses)} bar, {len(shell_stresses)} shell stresses")

            # Combine all stresses from all BDFs
            stresses = all_stresses
            if not stresses:
                self.log("  WARNING: No stress data extracted! Check if OP2 files exist.")
                op2_files = [f for f in os.listdir(folder) if f.lower().endswith('.op2')]
                self.log(f"    OP2 files found: {op2_files}")
            else:
                total_bar = sum(1 for s in stresses if s['type'] == 'bar')
                total_shell = sum(1 for s in stresses if s['type'] == 'shell')
                self.log(f"\n  Total stresses from all BDFs: {total_bar} bar, {total_shell} shell")

            # 4.5 Combine stresses using Residual Strength (if loaded)
            combined_stresses = None
            if self.residual_strength_df is not None:
                self.log("  [4.5] Combining stresses...")
                combined_stresses = self._combine_stresses_multi(folder, n_bdfs)
                if combined_stresses:
                    self.log(f"    Combined: {len(combined_stresses)} stress combinations")

            # 5. Calculate RF
            self.log("  [5] Calculating RF...")
            rf_results = self._calculate_rf(stresses, target_rf, combined_stresses)

            # 6. Calculate weight
            self.log("  [6] Calculating weight...")
            weight = self._calculate_weight()

            min_rf = rf_results['min_rf']
            n_fail = rf_results['n_fail']

            self.log(f"\n  Results: Min RF={min_rf:.4f}, Fails={n_fail}, Weight={weight:.6f}t")

            result = {
                'iteration': iteration,
                'min_rf': min_rf,
                'n_fail': n_fail,
                'weight': weight,
                'folder': folder,
                'bar_thicknesses': self.current_bar_thicknesses.copy(),
                'skin_thicknesses': self.current_skin_thicknesses.copy(),
                'rf_details': rf_results['details'],
                'failing_pids': rf_results['failing_pids']
            }

            self._save_iteration(folder, result)
            return result

        except Exception as e:
            self.log(f"  ERROR: {e}")
            return None

    def _write_bdf(self, folder):
        """Write BDF with updated thicknesses - dim1 updated, dim2 kept original."""
        input_bdf = self.input_bdf_path.get()
        output_bdf = os.path.join(folder, "model.bdf")

        with open(input_bdf, 'r', encoding='latin-1') as f:
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
                        # Ensure thickness is positive
                        t = max(0.1, t)
                        new_lines.append(line)
                        i += 1
                        # Process continuation lines
                        while i < len(lines) and (lines[i].startswith('+') or lines[i].startswith('*') or (lines[i][0] == ' ' and lines[i].strip() and not lines[i].strip().startswith('$'))):
                            cont = lines[i]
                            if cont.strip() and not cont.strip().startswith('$'):
                                # Parse original dim2 value (keep it)
                                try:
                                    # Original format: +name   DIM1    DIM2    ...
                                    # Field positions: 0-8=cont name, 8-16=DIM1, 16-24=DIM2
                                    original_dim2 = cont[16:24].strip()
                                    if original_dim2:
                                        dim2_val = float(original_dim2)
                                    else:
                                        dim2_val = t  # fallback
                                except:
                                    dim2_val = t  # fallback if parsing fails

                                # Write: continuation + new DIM1 + original DIM2 + rest
                                cont_name = cont[:8]
                                rest = cont[24:] if len(cont) > 24 else '\n'
                                new_cont = f"{cont_name}{t:8.4f}{dim2_val:8.4f}{rest}"
                                new_lines.append(new_cont)
                            else:
                                new_lines.append(cont)
                            i += 1
                        continue
                except Exception as e:
                    pass

            elif line.startswith('PSHELL'):
                try:
                    pid = int(line[8:16].strip())
                    if pid in self.current_skin_thicknesses:
                        t = self.current_skin_thicknesses[pid]
                        # Ensure thickness is positive
                        t = max(0.1, t)
                        # PSHELL format: PSHELL  PID     MID1    T       ...
                        # Field: 0-8=PSHELL, 8-16=PID, 16-24=MID1, 24-32=T
                        new_line = line[:24] + f"{t:8.4f}" + line[32:]
                        new_lines.append(new_line)
                        i += 1
                        continue
                except:
                    pass

            new_lines.append(line)
            i += 1

        with open(output_bdf, 'w', encoding='latin-1') as f:
            f.writelines(new_lines)

        self.log(f"    BDF written: {output_bdf}")
        return output_bdf

    def _write_bdf_for_model(self, folder, model, original_path):
        """Write BDF with updated thicknesses for a specific model (multi-BDF support)."""
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
                        while i < len(lines) and (lines[i].startswith('+') or lines[i].startswith('*') or (lines[i][0] == ' ' and lines[i].strip() and not lines[i].strip().startswith('$'))):
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

    def _apply_offsets(self, bdf_path, folder):
        """Apply landing zoffset and bar WA/WB offsets to BDF."""
        if not self.landing_elem_ids and not self.bar_offset_elem_ids:
            self.log("    No offset elements defined, skipping offset application")
            return bdf_path

        try:
            self.log(f"    Loading BDF for offset calculation...")
            bdf = BDF(debug=False)
            bdf.read_bdf(bdf_path, validate=False, xref=True, read_includes=True, encoding='latin-1')

            # Calculate landing (shell) offsets: zoffset = -t/2
            landing_offsets = {}
            landing_normals = {}

            for eid in self.landing_elem_ids:
                if eid not in bdf.elements:
                    continue
                elem = bdf.elements[eid]
                pid = elem.pid if hasattr(elem, 'pid') else None
                if pid is None:
                    continue

                t = self.current_skin_thicknesses.get(pid, float(self.skin_min_thickness.get()))
                t = max(0.1, t)  # Ensure positive
                landing_offsets[eid] = -t / 2.0

                # Calculate normal vector for bar offset calculation
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

            self.log(f"    Landing offsets calculated: {len(landing_offsets)} elements")

            # Build node -> shell mapping for bar offset calculation
            node_to_shells = {}
            for eid, elem in bdf.elements.items():
                if elem.type in ['CQUAD4', 'CTRIA3']:
                    for nid in elem.node_ids:
                        if nid not in node_to_shells:
                            node_to_shells[nid] = []
                        node_to_shells[nid].append(eid)

            # Calculate bar offsets: WA = WB = -normal * (landing_t + bar_t/2)
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
                bar_t = max(0.1, bar_t)  # Ensure positive

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
                        # Offset = landing_thickness + bar_thickness/2
                        offset_mag = max_t + bar_t / 2.0
                        bar_offsets[eid] = tuple(-best_normal * offset_mag)

            self.log(f"    Bar offsets calculated: {len(bar_offsets)} elements")

            # Apply offsets to BDF file
            with open(bdf_path, 'r', encoding='latin-1') as f:
                lines = f.readlines()

            def fmt(v, w=8):
                """Format value for Nastran field."""
                s = f"{v:.4f}"
                return s[:w].ljust(w) if len(s) <= w else f"{v:.2E}"[:w].ljust(w)

            new_lines = []
            i = 0
            applied_landing = 0
            applied_bar = 0

            while i < len(lines):
                line = lines[i]

                # CQUAD4: Apply zoffset at field 9 (position 64-72)
                if line.startswith('CQUAD4'):
                    try:
                        eid = int(line[8:16].strip())
                        if eid in landing_offsets:
                            # Ensure line is long enough
                            padded = line.rstrip().ljust(72)
                            new_line = padded[:64] + fmt(landing_offsets[eid]) + '\n'
                            new_lines.append(new_line)
                            applied_landing += 1
                            i += 1
                            continue
                    except:
                        pass

                # CTRIA3: Apply zoffset at field 7 (position 48-56)
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

                # CBAR: Apply WA, WB offset vectors as continuation
                elif line.startswith('CBAR'):
                    try:
                        eid = int(line[8:16].strip())
                        if eid in bar_offsets:
                            offset_vec = bar_offsets[eid]

                            # Check if next line is continuation (multi-line CBAR)
                            if i + 1 < len(lines) and (lines[i+1].startswith('+') or lines[i+1].startswith('*') or (lines[i+1][0] == ' ' and lines[i+1].strip())):
                                # Multi-line CBAR - modify existing continuation line
                                # Keep first 24 chars (cont marker + PA + PB), replace WA/WB
                                cont_line = lines[i+1]
                                # Ensure cont_line is at least 24 chars
                                if len(cont_line) < 24:
                                    cont_line = cont_line.rstrip().ljust(24)
                                new_cont = cont_line[:24]  # Keep +marker, PA, PB
                                new_cont += fmt(offset_vec[0])  # W1A (pos 24-32)
                                new_cont += fmt(offset_vec[1])  # W2A (pos 32-40)
                                new_cont += fmt(offset_vec[2])  # W3A (pos 40-48)
                                new_cont += fmt(offset_vec[0])  # W1B (pos 48-56)
                                new_cont += fmt(offset_vec[1])  # W2B (pos 56-64)
                                new_cont += fmt(offset_vec[2])  # W3B (pos 64-72)
                                new_cont += '\n'

                                new_lines.append(line)
                                new_lines.append(new_cont)
                                applied_bar += 1
                                i += 2
                                continue
                            else:
                                # Single line CBAR - add continuation for offsets
                                # Add continuation marker to main line
                                cont_name = '+CB' + str(eid)[-4:]
                                new_lines.append(line.rstrip() + cont_name + '\n')

                                # Create continuation line: +name, PA(blank), PB(blank), W1A, W2A, W3A, W1B, W2B, W3B
                                new_cont = cont_name.ljust(8)      # pos 0-7: continuation name
                                new_cont += '        '              # pos 8-15: PA (blank)
                                new_cont += '        '              # pos 16-23: PB (blank)
                                new_cont += fmt(offset_vec[0])     # pos 24-31: W1A
                                new_cont += fmt(offset_vec[1])     # pos 32-39: W2A
                                new_cont += fmt(offset_vec[2])     # pos 40-47: W3A
                                new_cont += fmt(offset_vec[0])     # pos 48-55: W1B
                                new_cont += fmt(offset_vec[1])     # pos 56-63: W2B
                                new_cont += fmt(offset_vec[2])     # pos 64-71: W3B
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
            self.log(f"    Offset BDF written: {output_bdf}")

            return output_bdf

        except Exception as e:
            self.log(f"    Offset error: {e}")
            return bdf_path

    def _run_nastran(self, bdf_path, folder):
        nastran = self.nastran_path.get()
        if not nastran or not os.path.exists(nastran):
            return False
        try:
            cmd = f'"{nastran}" "{bdf_path}" out="{folder}" scratch=yes batch=no'
            proc = subprocess.Popen(cmd, shell=True)
            proc.wait(timeout=600)
            return True
        except:
            return False

    def _extract_stresses(self, folder):
        """Extract stresses from OP2 using cbar_force (RF Check Tool logic)."""
        results = []
        bar_stress_rows = []  # For bar_stress_results.csv

        for f in os.listdir(folder):
            if f.lower().endswith('.op2'):
                op2_name = f
                try:
                    op2 = OP2(debug=False)
                    op2.read_op2(os.path.join(folder, f))

                    # BAR STRESS from cbar_force (RF Check Tool exact logic)
                    if hasattr(op2, 'cbar_force') and op2.cbar_force:
                        for sc_id, force in op2.cbar_force.items():
                            for i, eid in enumerate(force.element):
                                # Axial force at index 6 (bending moment MA1)
                                axial = force.data[0, i, 6] if len(force.data.shape) == 3 else force.data[i, 6]
                                pid = self.elem_to_prop.get(int(eid))
                                d1 = d2 = area = stress = None

                                # Get dimensions: dim1 from current optimization, dim2 from BDF PBARL
                                if pid and pid in self.bar_properties:
                                    d1 = self.current_bar_thicknesses.get(pid, self.bar_properties[pid].get('dim1', 0))
                                    # Use BDF PBARL dim2 (original geometry), fallback to Excel
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

                                bar_stress_rows.append({
                                    'OP2': op2_name, 'Subcase': int(sc_id), 'Element': int(eid),
                                    'Property': pid, 'Axial': float(axial) if axial else 0,
                                    'Dim1': d1, 'Dim2': d2, 'Area': area,
                                    'Stress': float(stress) if stress else None
                                })

                    # SHELL STRESS - try multiple stress result types
                    shell_stress_count = 0

                    # List of shell stress attributes to try
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
                                        # Try to get von Mises stress (usually last column)
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
                                            shell_stress_count += 1
                                        except Exception:
                                            pass

                    # Log available stress attributes for debugging
                    if shell_stress_count == 0:
                        available_attrs = [attr for attr in dir(op2) if 'stress' in attr.lower() and not attr.startswith('_')]
                        self.log(f"    DEBUG: No shell stress found. Available: {available_attrs[:10]}")

                except Exception as e:
                    self.log(f"    OP2 read error: {e}")

        # Save bar_stress_results.csv
        if bar_stress_rows:
            csv_path = os.path.join(folder, 'bar_stress_results.csv')
            with open(csv_path, 'w', newline='') as f:
                w = csv.DictWriter(f, fieldnames=['OP2', 'Subcase', 'Element', 'Property', 'Axial', 'Dim1', 'Dim2', 'Area', 'Stress'])
                w.writeheader()
                w.writerows(bar_stress_rows)
            self.log(f"    Saved: bar_stress_results.csv ({len(bar_stress_rows)} rows)")

        return results

    def _combine_stresses(self, folder):
        """Combine stresses using Residual Strength table (RF Check Tool logic)."""
        if self.residual_strength_df is None or len(self.combination_table) == 0:
            self.log("    No Residual Strength data - skipping combination")
            return None

        stress_csv = os.path.join(folder, 'bar_stress_results.csv')
        if not os.path.exists(stress_csv):
            self.log("    bar_stress_results.csv not found")
            return None

        try:
            stress_df = pd.read_csv(stress_csv)

            # Build lookup: (subcase, element) -> stress
            lookup = {}
            for _, row in stress_df.iterrows():
                key = (int(row['Subcase']), int(row['Element']))
                lookup[key] = row['Stress'] if pd.notna(row['Stress']) else 0

            elements = stress_df['Element'].unique()

            rs_df = self.residual_strength_df
            cols = rs_df.columns.tolist()
            comb_col = cols[0]  # First column is Combined LC

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
                        results.append({
                            'Combined_LC': comb_lc, 'Element': int(eid),
                            'Combined_Stress': total_stress,
                            'Components': ' + '.join(components)
                        })

            # Save combined_stress_results.csv
            if results:
                comb_csv = os.path.join(folder, 'combined_stress_results.csv')
                with open(comb_csv, 'w', newline='') as f:
                    w = csv.DictWriter(f, fieldnames=['Combined_LC', 'Element', 'Combined_Stress', 'Components'])
                    w.writeheader()
                    w.writerows(results)
                self.log(f"    Saved: combined_stress_results.csv ({len(results)} rows)")
                return results

        except Exception as e:
            self.log(f"    Combine error: {e}")

        return None

    def _combine_stresses_multi(self, folder, n_bdfs):
        """Combine stresses from multiple BDFs using Residual Strength table."""
        if self.residual_strength_df is None or len(self.combination_table) == 0:
            self.log("    No Residual Strength data - skipping combination")
            return None

        try:
            # Collect stress data from all BDF subfolders
            all_stress_data = []

            if n_bdfs > 1:
                # Look for subfolders
                for item in os.listdir(folder):
                    subfolder = os.path.join(folder, item)
                    if os.path.isdir(subfolder) and item.startswith('bdf_'):
                        stress_csv = os.path.join(subfolder, 'bar_stress_results.csv')
                        if os.path.exists(stress_csv):
                            df = pd.read_csv(stress_csv)
                            all_stress_data.append(df)
                            self.log(f"    Loaded stresses from: {item}")
            else:
                # Single BDF case
                stress_csv = os.path.join(folder, 'bar_stress_results.csv')
                if os.path.exists(stress_csv):
                    all_stress_data.append(pd.read_csv(stress_csv))

            if not all_stress_data:
                self.log("    No bar_stress_results.csv found in any BDF folder")
                return None

            # Merge all stress data
            stress_df = pd.concat(all_stress_data, ignore_index=True)
            self.log(f"    Combined stress data: {len(stress_df)} rows from {len(all_stress_data)} BDFs")

            # Build lookup: (subcase, element) -> stress (use max stress if duplicates)
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
                        results.append({
                            'Combined_LC': comb_lc, 'Element': int(eid),
                            'Combined_Stress': total_stress,
                            'Components': ' + '.join(components)
                        })

            # Save combined results
            if results:
                comb_csv = os.path.join(folder, 'combined_stress_results.csv')
                with open(comb_csv, 'w', newline='') as f:
                    w = csv.DictWriter(f, fieldnames=['Combined_LC', 'Element', 'Combined_Stress', 'Components'])
                    w.writeheader()
                    w.writerows(results)
                self.log(f"    Saved: combined_stress_results.csv ({len(results)} rows)")
                return results

        except Exception as e:
            self.log(f"    Multi-BDF combine error: {e}")

        return None

    def _calculate_rf(self, stresses, target_rf, combined_stresses=None):
        """Calculate RF using combined stresses if available, otherwise raw stresses."""
        details = []
        failing_pids = set()
        elem_fit = prop_fit = 0

        # If combined stresses are available, build lookup
        combined_lookup = {}
        if combined_stresses:
            # Find max combined stress per element (critical case)
            for cs in combined_stresses:
                eid = cs['Element']
                comb_stress = abs(cs['Combined_Stress'])
                if eid not in combined_lookup or comb_stress > combined_lookup[eid]:
                    combined_lookup[eid] = comb_stress

        for s in stresses:
            eid = s['eid']
            etype = s['type']
            pid = self.elem_to_prop.get(eid)

            # Use combined stress if available, otherwise use raw stress
            if eid in combined_lookup and etype == 'bar':
                stress = combined_lookup[eid]
                stress_src = 'combined'
            else:
                stress = abs(s['stress'])
                stress_src = 'raw'

            if etype == 'bar' and pid:
                t = self.current_bar_thicknesses.get(pid, float(self.bar_min_thickness.get()))
            else:
                t = self.current_skin_thicknesses.get(pid, float(self.skin_min_thickness.get())) if pid else float(self.skin_min_thickness.get())

            # Try element fit first, then property fit
            allowable = None
            fit_src = "none"

            if eid in self.allowable_elem_interp:
                allowable = self.get_allowable_stress_elem(eid, t)
                if allowable:
                    fit_src = "element"
                    elem_fit += 1

            if allowable is None and pid:
                allowable = self.get_allowable_stress(pid, t)
                if allowable:
                    fit_src = "property"
                    prop_fit += 1

            if stress == 0:
                rf = 999.0
                status = 'PASS'
            elif allowable and allowable > 0:
                rf = allowable / stress
                status = 'PASS' if rf >= target_rf else 'FAIL'
            else:
                rf = 0
                status = 'NO_ALLOW'

            if status == 'FAIL' and pid:
                failing_pids.add(pid)

            req_t = self.get_required_thickness(pid, stress, target_rf) if pid and status == 'FAIL' else None

            details.append({
                'eid': eid, 'pid': pid, 'type': etype, 'thickness': t,
                'stress': stress, 'allowable': allowable, 'rf': rf,
                'status': status, 'fit_src': fit_src, 'req_thickness': req_t,
                'stress_src': stress_src
            })

        valid_rf = [d['rf'] for d in details if 0 < d['rf'] < 999]
        min_rf = min(valid_rf) if valid_rf else 0
        n_fail = sum(1 for d in details if d['status'] == 'FAIL')

        return {'min_rf': min_rf, 'n_fail': n_fail, 'details': details, 'failing_pids': failing_pids}

    def _calculate_weight(self):
        weight = 0.0

        for pid in self.skin_properties:
            t = self.current_skin_thicknesses.get(pid, 0)
            rho = self.get_density(pid)
            if pid in self.prop_elements:
                area = sum(self.element_areas.get(eid, 0) for eid in self.prop_elements[pid])
                weight += area * t * rho

        for pid in self.bar_properties:
            dim1 = self.current_bar_thicknesses.get(pid, 0)  # Optimized dimension
            # Use BDF PBARL dim2 (original geometry), fallback to Excel
            if pid in self.pbarl_dims:
                dim2 = self.pbarl_dims[pid]['dim2']
            else:
                dim2 = self.bar_properties[pid].get('dim2', dim1)
            rho = self.get_density(pid)
            if pid in self.prop_elements:
                length = sum(self.bar_lengths.get(eid, 0) for eid in self.prop_elements[pid])
                # Cross-sectional area = dim1 * dim2 for rectangular bar
                weight += length * dim1 * dim2 * rho

        return weight

    def _smart_thickness_update(self, result, step, bar_min, bar_max, skin_min, skin_max, target_rf, rf_tol):
        """Per-property smart thickness update based on RF sensitivity."""
        details = result.get('rf_details', [])
        failing_pids = result.get('failing_pids', set())

        # Group by PID and find min RF per property
        pid_data = {}
        for d in details:
            pid = d['pid']
            if pid is None:
                continue
            if pid not in pid_data:
                pid_data[pid] = {'min_rf': 999, 'max_stress': 0, 'req_thickness': None}
            if d['rf'] < pid_data[pid]['min_rf']:
                pid_data[pid]['min_rf'] = d['rf']
                pid_data[pid]['max_stress'] = d['stress']
                pid_data[pid]['req_thickness'] = d.get('req_thickness')

        updated = 0

        # Increase failing properties
        for pid in failing_pids:
            if pid in self.current_bar_thicknesses:
                current = self.current_bar_thicknesses[pid]
                req_t = pid_data.get(pid, {}).get('req_thickness')
                if req_t and req_t > current:
                    new_t = min(req_t * 1.05, bar_max)  # 5% margin
                else:
                    new_t = min(current + step, bar_max)
                if new_t > current:
                    self.current_bar_thicknesses[pid] = new_t
                    updated += 1

            elif pid in self.current_skin_thicknesses:
                current = self.current_skin_thicknesses[pid]
                req_t = pid_data.get(pid, {}).get('req_thickness')
                if req_t and req_t > current:
                    new_t = min(req_t * 1.05, skin_max)
                else:
                    new_t = min(current + step, skin_max)
                if new_t > current:
                    self.current_skin_thicknesses[pid] = new_t
                    updated += 1

        # Decrease over-designed properties (RF > target + tolerance + 0.2)
        reduce_threshold = target_rf + rf_tol + 0.2
        for pid, data in pid_data.items():
            if data['min_rf'] > reduce_threshold and pid not in failing_pids:
                if pid in self.current_bar_thicknesses:
                    current = self.current_bar_thicknesses[pid]
                    new_t = max(current - step/2, bar_min)
                    if new_t < current:
                        self.current_bar_thicknesses[pid] = new_t
                        updated += 1

                elif pid in self.current_skin_thicknesses:
                    current = self.current_skin_thicknesses[pid]
                    new_t = max(current - step/2, skin_min)
                    if new_t < current:
                        self.current_skin_thicknesses[pid] = new_t
                        updated += 1

        if updated:
            self.log(f"  Updated {updated} properties")
        else:
            self.log(f"  No property updates needed (failing: {len(failing_pids)}, at max: {sum(1 for p in failing_pids if (p in self.current_bar_thicknesses and self.current_bar_thicknesses[p] >= bar_max) or (p in self.current_skin_thicknesses and self.current_skin_thicknesses[p] >= skin_max))})")

    def _save_iteration(self, folder, result):
        try:
            with open(os.path.join(folder, "summary.csv"), 'w', newline='') as f:
                w = csv.writer(f)
                w.writerow(['Parameter', 'Value'])
                w.writerow(['Iteration', result['iteration']])
                w.writerow(['Min_RF', result['min_rf']])
                w.writerow(['N_Fail', result['n_fail']])
                w.writerow(['Weight', result['weight']])

            pd.DataFrame(result['rf_details']).to_csv(os.path.join(folder, "rf_details.csv"), index=False)

            bar_data = [{'PID': p, 'Thickness': t} for p, t in result['bar_thicknesses'].items()]
            skin_data = [{'PID': p, 'Thickness': t} for p, t in result['skin_thicknesses'].items()]
            pd.DataFrame(bar_data).to_csv(os.path.join(folder, "bar_thicknesses.csv"), index=False)
            pd.DataFrame(skin_data).to_csv(os.path.join(folder, "skin_thicknesses.csv"), index=False)

        except Exception as e:
            self.log(f"  Save error: {e}")

    def _save_results(self, folder):
        try:
            history = [{'iteration': r['iteration'], 'min_rf': r['min_rf'], 'n_fail': r['n_fail'], 'weight': r['weight']} for r in self.iteration_results]
            pd.DataFrame(history).to_csv(os.path.join(folder, "history.csv"), index=False)

            if self.best_solution:
                pd.DataFrame([{'iteration': self.best_solution['iteration'], 'min_rf': self.best_solution['min_rf'], 'weight': self.best_solution['weight']}]).to_csv(os.path.join(folder, "best.csv"), index=False)

        except Exception as e:
            self.log(f"Save error: {e}")

    def _generate_final_report(self, folder, algorithm_name, nastran_count=None, extra_info=None):
        """Generate comprehensive final optimization report."""
        if not self.best_solution:
            self.log("No best solution found - cannot generate report")
            return

        report_lines = []
        sep = "═" * 70

        # Header
        report_lines.append("")
        report_lines.append(sep)
        report_lines.append("              OPTIMIZATION FINAL REPORT")
        report_lines.append(sep)
        report_lines.append(f"  Algorithm: {algorithm_name}")
        report_lines.append(f"  Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
        report_lines.append(sep)

        # Best Solution Summary
        report_lines.append("")
        report_lines.append("  BEST SOLUTION FOUND:")
        report_lines.append("  " + "-" * 40)
        report_lines.append(f"    Iteration/Evaluation: {self.best_solution['iteration']}")
        report_lines.append(f"    Minimum RF: {self.best_solution['min_rf']:.4f}")
        report_lines.append(f"    Total Weight: {self.best_solution['weight']:.6f} tonnes")
        report_lines.append(f"    Failed Elements: {self.best_solution['n_fail']}")

        target_rf = float(self.target_rf.get())
        if self.best_solution['min_rf'] >= target_rf:
            report_lines.append(f"    Status: ✓ CONVERGED (RF >= {target_rf})")
        else:
            report_lines.append(f"    Status: ✗ NOT CONVERGED (RF < {target_rf})")

        # Bar Thickness Changes
        bar_min = float(self.bar_min_thickness.get())
        report_lines.append("")
        report_lines.append("  BAR THICKNESS RESULTS:")
        report_lines.append("  " + "-" * 40)
        report_lines.append(f"    {'PID':<10} {'Initial':>10} {'Final':>10} {'Change':>12}")
        report_lines.append("    " + "-" * 44)

        bar_thicknesses = self.best_solution.get('bar_thicknesses', {})
        total_bar_increase = 0
        for pid in sorted(bar_thicknesses.keys()):
            final_t = bar_thicknesses[pid]
            initial_t = bar_min
            change_pct = ((final_t - initial_t) / initial_t * 100) if initial_t > 0 else 0
            total_bar_increase += (final_t - initial_t)
            report_lines.append(f"    {pid:<10} {initial_t:>10.2f} {final_t:>10.2f} {change_pct:>+10.1f}%")

        if bar_thicknesses:
            avg_bar = sum(bar_thicknesses.values()) / len(bar_thicknesses)
            report_lines.append("    " + "-" * 44)
            report_lines.append(f"    {'Average':<10} {bar_min:>10.2f} {avg_bar:>10.2f}")

        # Skin Thickness Changes
        skin_min = float(self.skin_min_thickness.get())
        skin_thicknesses = self.best_solution.get('skin_thicknesses', {})
        if skin_thicknesses:
            report_lines.append("")
            report_lines.append("  SKIN THICKNESS RESULTS:")
            report_lines.append("  " + "-" * 40)
            report_lines.append(f"    {'PID':<10} {'Initial':>10} {'Final':>10} {'Change':>12}")
            report_lines.append("    " + "-" * 44)

            for pid in sorted(skin_thicknesses.keys()):
                final_t = skin_thicknesses[pid]
                initial_t = skin_min
                change_pct = ((final_t - initial_t) / initial_t * 100) if initial_t > 0 else 0
                report_lines.append(f"    {pid:<10} {initial_t:>10.2f} {final_t:>10.2f} {change_pct:>+10.1f}%")

            avg_skin = sum(skin_thicknesses.values()) / len(skin_thicknesses)
            report_lines.append("    " + "-" * 44)
            report_lines.append(f"    {'Average':<10} {skin_min:>10.2f} {avg_skin:>10.2f}")

        # RF Statistics
        rf_details = self.best_solution.get('rf_details', [])
        if rf_details:
            valid_rfs = [d['rf'] for d in rf_details if d['rf'] is not None and 0 < d['rf'] < 999]
            if valid_rfs:
                report_lines.append("")
                report_lines.append("  RF STATISTICS:")
                report_lines.append("  " + "-" * 40)
                report_lines.append(f"    Minimum RF: {min(valid_rfs):.4f}")
                report_lines.append(f"    Maximum RF: {max(valid_rfs):.4f}")
                report_lines.append(f"    Average RF: {sum(valid_rfs)/len(valid_rfs):.4f}")
                report_lines.append(f"    Total Elements Analyzed: {len(rf_details)}")

                # RF Distribution
                below_target = sum(1 for rf in valid_rfs if rf < target_rf)
                near_target = sum(1 for rf in valid_rfs if target_rf <= rf < target_rf + 0.2)
                above_target = sum(1 for rf in valid_rfs if rf >= target_rf + 0.2)

                report_lines.append("")
                report_lines.append(f"    RF Distribution:")
                report_lines.append(f"      Below target (RF < {target_rf}): {below_target} elements")
                report_lines.append(f"      Near target ({target_rf} ≤ RF < {target_rf+0.2}): {near_target} elements")
                report_lines.append(f"      Above target (RF ≥ {target_rf+0.2}): {above_target} elements")

                # Critical elements (lowest RF)
                report_lines.append("")
                report_lines.append("    Critical Elements (Lowest RF):")
                sorted_details = sorted([d for d in rf_details if d['rf'] and 0 < d['rf'] < 999],
                                       key=lambda x: x['rf'])[:5]
                for d in sorted_details:
                    report_lines.append(f"      EID {d['eid']}: RF={d['rf']:.4f}, PID={d['pid']}, Stress={d['stress']:.2f}")

        # Convergence Info
        report_lines.append("")
        report_lines.append("  CONVERGENCE INFO:")
        report_lines.append("  " + "-" * 40)

        if nastran_count:
            report_lines.append(f"    Total Nastran Evaluations: {nastran_count}")

        if self.iteration_results:
            first_result = self.iteration_results[0]
            report_lines.append(f"    Initial Min RF: {first_result['min_rf']:.4f}")
            report_lines.append(f"    Final Min RF: {self.best_solution['min_rf']:.4f}")
            rf_improvement = self.best_solution['min_rf'] - first_result['min_rf']
            report_lines.append(f"    RF Improvement: {rf_improvement:+.4f}")

            report_lines.append(f"    Initial Weight: {first_result['weight']:.6f} t")
            report_lines.append(f"    Final Weight: {self.best_solution['weight']:.6f} t")
            weight_change = ((self.best_solution['weight'] - first_result['weight']) / first_result['weight'] * 100) if first_result['weight'] > 0 else 0
            report_lines.append(f"    Weight Change: {weight_change:+.1f}%")

        # Extra algorithm-specific info
        if extra_info:
            report_lines.append("")
            report_lines.append("  ALGORITHM SPECIFIC:")
            report_lines.append("  " + "-" * 40)
            for key, value in extra_info.items():
                report_lines.append(f"    {key}: {value}")

        # Footer
        report_lines.append("")
        report_lines.append(sep)
        report_lines.append(f"  Report saved to: {folder}")
        report_lines.append(sep)
        report_lines.append("")

        # Join and display
        report_text = "\n".join(report_lines)
        self.log(report_text)

        # Save to file
        try:
            report_path = os.path.join(folder, "FINAL_REPORT.txt")
            with open(report_path, 'w', encoding='utf-8') as f:
                f.write(report_text)
            self.log(f"Report saved to: {report_path}")

            # Also save detailed thickness CSV
            thickness_data = []
            for pid, t in bar_thicknesses.items():
                thickness_data.append({
                    'Type': 'BAR',
                    'PID': pid,
                    'Initial_mm': bar_min,
                    'Final_mm': t,
                    'Change_pct': ((t - bar_min) / bar_min * 100) if bar_min > 0 else 0
                })
            for pid, t in skin_thicknesses.items():
                thickness_data.append({
                    'Type': 'SKIN',
                    'PID': pid,
                    'Initial_mm': skin_min,
                    'Final_mm': t,
                    'Change_pct': ((t - skin_min) / skin_min * 100) if skin_min > 0 else 0
                })
            if thickness_data:
                pd.DataFrame(thickness_data).to_csv(os.path.join(folder, "final_thicknesses.csv"), index=False)

        except Exception as e:
            self.log(f"Error saving report: {e}")

    def _update_ui(self):
        if self.best_solution:
            self.result_summary.config(text=f"Best: Weight={self.best_solution['weight']:.6f}t, RF={self.best_solution['min_rf']:.4f}", foreground="green")

            self.best_text.delete(1.0, tk.END)
            txt = f"Best Solution (Iteration {self.best_solution['iteration']}):\n"
            txt += f"  Weight: {self.best_solution['weight']:.6f} tonnes\n"
            txt += f"  Min RF: {self.best_solution['min_rf']:.4f}\n"
            txt += f"  Failures: {self.best_solution['n_fail']}\n\n"

            txt += "Bar Thicknesses (sample):\n"
            for pid in list(self.best_solution['bar_thicknesses'].keys())[:10]:
                txt += f"  PID {pid}: {self.best_solution['bar_thicknesses'][pid]:.2f} mm\n"

            txt += "\nSkin Thicknesses (sample):\n"
            for pid in list(self.best_solution['skin_thicknesses'].keys())[:10]:
                txt += f"  PID {pid}: {self.best_solution['skin_thicknesses'][pid]:.2f} mm\n"

            self.best_text.insert(tk.END, txt)

    def export_results(self):
        if not self.iteration_results:
            messagebox.showerror("Error", "No results")
            return

        try:
            ts = datetime.now().strftime("%Y%m%d_%H%M%S")
            path = os.path.join(self.output_folder.get(), f"results_{ts}.xlsx")

            with pd.ExcelWriter(path, engine='openpyxl') as w:
                history = [{'iteration': r['iteration'], 'min_rf': r['min_rf'], 'n_fail': r['n_fail'], 'weight': r['weight']} for r in self.iteration_results]
                pd.DataFrame(history).to_excel(w, sheet_name='History', index=False)

                if self.best_solution:
                    bar_data = [{'PID': p, 'Thickness': t} for p, t in self.best_solution['bar_thicknesses'].items()]
                    skin_data = [{'PID': p, 'Thickness': t} for p, t in self.best_solution['skin_thicknesses'].items()]
                    pd.DataFrame(bar_data).to_excel(w, sheet_name='Bar_Thicknesses', index=False)
                    pd.DataFrame(skin_data).to_excel(w, sheet_name='Skin_Thicknesses', index=False)

            self.log(f"\nExported: {path}")
            messagebox.showinfo("Export", f"Saved to:\n{path}")

        except Exception as e:
            self.log(f"Export error: {e}")


def main():
    root = tk.Tk()
    app = ThicknessIterationTool(root)
    root.mainloop()


if __name__ == "__main__":
    main()
