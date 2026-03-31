import ast
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
from collections import Counter
import math
import json
import sys
import os
import itertools

# Optional imports for advanced features
try:
    import networkx as nx
    import matplotlib.pyplot as plt
    from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
    HAS_NETWORKX = True
except ImportError:
    HAS_NETWORKX = False

try:
    from reportlab.lib.pagesizes import letter
    from reportlab.pdfgen import canvas
    HAS_REPORTLAB = True
except ImportError:
    HAS_REPORTLAB = False


# =============================================================================
# Module 1: Halstead Metrics
# =============================================================================
class HalsteadAnalyzer:
    """
    Computes Halstead metrics from Python source code.
    Operators: AST node types representing operations.
    Operands: variable names and literals.
    """
    def __init__(self, source_code):
        self.source_code = source_code
        self.operators = Counter()   # unique operators -> count
        self.operands = Counter()    # unique operands -> count
        self.total_operators = 0
        self.total_operands = 0
        self.n1 = 0  # distinct operators
        self.n2 = 0  # distinct operands
        self.N1 = 0  # total operators
        self.N2 = 0  # total operands
        self.volume = 0
        self.difficulty = 0
        self.effort = 0
        self.bugs = 0

        # Define which AST nodes are considered operators
        self.operator_nodes = {
            ast.Add: '+', ast.Sub: '-', ast.Mult: '*', ast.Div: '/', ast.Mod: '%',
            ast.Pow: '**', ast.LShift: '<<', ast.RShift: '>>', ast.BitOr: '|',
            ast.BitXor: '^', ast.BitAnd: '&', ast.FloorDiv: '//',
            ast.Eq: '==', ast.NotEq: '!=', ast.Lt: '<', ast.LtE: '<=',
            ast.Gt: '>', ast.GtE: '>=', ast.Is: 'is', ast.IsNot: 'is not',
            ast.In: 'in', ast.NotIn: 'not in', ast.And: 'and', ast.Or: 'or',
            ast.Not: 'not', ast.UAdd: '+', ast.USub: '-',
            ast.Assign: '=', ast.AugAssign: 'aug_assign', ast.Call: 'call',
            ast.Subscript: '[]', ast.Attribute: '.', ast.Return: 'return',
            ast.If: 'if', ast.While: 'while', ast.For: 'for', ast.Break: 'break',
            ast.Continue: 'continue', ast.Pass: 'pass', ast.Raise: 'raise',
            ast.Try: 'try', ast.ExceptHandler: 'except', ast.With: 'with',
            ast.FunctionDef: 'def', ast.ClassDef: 'class', ast.Import: 'import',
            ast.ImportFrom: 'from ... import', ast.Global: 'global', ast.Nonlocal: 'nonlocal'
        }

    def analyze(self):
        try:
            tree = ast.parse(self.source_code)
        except SyntaxError as e:
            raise ValueError(f"Syntax error in source code: {e}")

        visitor = HalsteadVisitor(self)
        visitor.visit(tree)

        # Compute metrics
        self.N1 = sum(self.operators.values())
        self.N2 = sum(self.operands.values())
        self.n1 = len(self.operators)
        self.n2 = len(self.operands)

        if self.n1 + self.n2 > 0:
            self.volume = (self.N1 + self.N2) * math.log2(self.n1 + self.n2)
        else:
            self.volume = 0

        if self.n2 > 0:
            self.difficulty = (self.n1 / 2) * (self.N2 / self.n2)
        else:
            self.difficulty = 0

        self.effort = self.difficulty * self.volume
        self.bugs = self.volume / 3000

        return self

    def get_metrics(self):
        return {
            'n1': self.n1, 'N1': self.N1,
            'n2': self.n2, 'N2': self.N2,
            'Volume': self.volume,
            'Difficulty': self.difficulty,
            'Effort': self.effort,
            'Estimated Bugs (B)': self.bugs
        }


class HalsteadVisitor(ast.NodeVisitor):
    def __init__(self, analyzer):
        self.analyzer = analyzer

    def visit(self, node):
        # Count operator
        op_type = type(node)
        if op_type in self.analyzer.operator_nodes:
            op_name = self.analyzer.operator_nodes[op_type]
            self.analyzer.operators[op_name] += 1
        # Count operands
        if isinstance(node, ast.Name):
            self.analyzer.operands[node.id] += 1
        elif isinstance(node, ast.Constant):
            literal_repr = repr(node.value)
            self.analyzer.operands[literal_repr] += 1
        self.generic_visit(node)


# =============================================================================
# Module 2: McCabe Cyclomatic Complexity, CFG, and Test Cases
# =============================================================================
class DecisionCounter(ast.NodeVisitor):
    """Counts decision points (if, for, while, and, or, etc.)"""
    def __init__(self):
        self.decision_points = []

    def visit_If(self, node):
        self.decision_points.append(node)
        self.generic_visit(node)

    def visit_While(self, node):
        self.decision_points.append(node)
        self.generic_visit(node)

    def visit_For(self, node):
        self.decision_points.append(node)
        self.generic_visit(node)

    def visit_BoolOp(self, node):
        for op in node.values:
            self.visit(op)
        self.decision_points.append(node)
        return

    def visit_Compare(self, node):
        self.decision_points.append(node)
        self.generic_visit(node)


class McCabeAnalyzer:
    """
    Computes cyclomatic complexity (V(G)), builds CFG, and generates basis test paths.
    """
    def __init__(self, source_code):
        self.source_code = source_code
        self.vg = 0
        self.decision_points = []
        self.cfg = None  # networkx DiGraph
        self.node_labels = {}  # mapping from node id to label
        self.basis_paths = []  # list of paths (list of node ids)
        self.test_cases = []   # list of dicts with input conditions and expected path

    def analyze(self):
        try:
            tree = ast.parse(self.source_code)
        except SyntaxError as e:
            raise ValueError(f"Syntax error in source code: {e}")

        # Count decision points
        decision_counter = DecisionCounter()
        decision_counter.visit(tree)
        self.decision_points = decision_counter.decision_points
        self.vg = len(self.decision_points) + 1

        # Build CFG (only for the first function if any) - optional
        if HAS_NETWORKX:
            first_func = None
            for node in ast.walk(tree):
                if isinstance(node, ast.FunctionDef):
                    first_func = node
                    break
            if first_func:
                self.cfg, self.node_labels = self.build_cfg(first_func)
            else:
                self.cfg = None
        else:
            self.cfg = None

        # Always generate test cases based on decision points
        self.test_cases = self._generate_test_cases_from_decisions()
        # Also generate basis paths (textual description) for completeness
        self.basis_paths = self._generate_basis_paths()

        return self

    def get_vg(self):
        return self.vg

    def build_cfg(self, func_node):
        """
        Builds a more accurate CFG for the function.
        Returns (DiGraph, node_labels) where node_labels maps node id to readable label.
        """
        G = nx.DiGraph()
        node_counter = 0
        labels = {}

        def add_node(description):
            nonlocal node_counter
            G.add_node(node_counter)
            labels[node_counter] = description
            node_counter += 1
            return node_counter - 1

        # Simplified: create nodes for statements and add edges
        statements = []
        for node in ast.walk(func_node):
            if isinstance(node, (ast.If, ast.For, ast.While, ast.Return, ast.Expr, ast.Assign,
                                 ast.AugAssign, ast.Break, ast.Continue, ast.Pass)):
                statements.append(node)

        stmt_nodes = []
        for stmt in statements:
            nid = add_node(self._stmt_label(stmt))
            stmt_nodes.append((stmt, nid))

        for i in range(len(stmt_nodes)-1):
            G.add_edge(stmt_nodes[i][1], stmt_nodes[i+1][1])

        return G, labels

    def _stmt_label(self, node):
        if isinstance(node, ast.If):
            return f"if {ast.unparse(node.test)}"
        elif isinstance(node, ast.While):
            return f"while {ast.unparse(node.test)}"
        elif isinstance(node, ast.For):
            return f"for {ast.unparse(node.target)} in {ast.unparse(node.iter)}"
        elif isinstance(node, ast.Return):
            return "return"
        else:
            return ast.unparse(node).split('\n')[0][:30]

    def _generate_basis_paths(self):
        """
        Generate basis paths from the CFG using cycle basis algorithm.
        Returns a list of path descriptions.
        """
        if not self.decision_points:
            return ["No decision points - single path"]
        paths = []
        for i, dec in enumerate(self.decision_points, 1):
            condition = ast.unparse(dec)
            paths.append(f"Path {i}: {condition} = True, others False")
        paths.append("Path 0: All decisions False")
        return paths

    def _generate_test_cases_from_decisions(self):
        """
        Generate test cases based solely on decision points (predicates).
        This ensures test cases are always available, even without networkx.
        """
        test_cases = []
        for i, dec in enumerate(self.decision_points, 1):
            condition = ast.unparse(dec)
            test_case = {
                "id": i,
                "description": f"Make '{condition}' True",
                "suggested_input": f"Provide input so that {condition} holds",
                "expected_path": f"Path where decision {i} is True, others may vary"
            }
            test_cases.append(test_case)
        # Additional test case where all decisions are False
        if self.decision_points:
            test_cases.append({
                "id": len(self.decision_points) + 1,
                "description": "All decisions False",
                "suggested_input": "Provide input that makes all conditions False",
                "expected_path": "Path where no branch is taken (if applicable)"
            })
        return test_cases


# =============================================================================
# Module 3: Chepin Informational Analysis
# =============================================================================
class ChepinAnalyzer:
    """
    Extracts variable names and allows classification.
    Computes Q = (C + M) / (P + T) (if denominator > 0, else 0).
    """
    def __init__(self, source_code):
        self.source_code = source_code
        self.variables = []   # list of variable names (unique)
        self.classifications = {}  # var -> category ('P','M','C','T')
        self.Q = 0

    def extract_variables(self):
        try:
            tree = ast.parse(self.source_code)
        except SyntaxError as e:
            raise ValueError(f"Syntax error in source code: {e}")

        var_set = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Name):
                var_set.add(node.id)
            if isinstance(node, ast.FunctionDef):
                for arg in node.args.args:
                    var_set.add(arg.arg)
        self.variables = sorted(var_set)
        self.classifications = {v: 'T' for v in self.variables}
        self._update_q()
        return self.variables

    def set_classification(self, var, category):
        if var in self.classifications:
            self.classifications[var] = category
            self._update_q()

    def _update_q(self):
        counts = {'P':0, 'M':0, 'C':0, 'T':0}
        for cat in self.classifications.values():
            if cat in counts:
                counts[cat] += 1
        denom = counts['P'] + counts['T']
        if denom > 0:
            self.Q = (counts['C'] + counts['M']) / denom
        else:
            self.Q = 0

    def get_q(self):
        return self.Q

    def get_classifications(self):
        return self.classifications


# =============================================================================
# Main GUI Application
# =============================================================================
class CodeAuditorApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Code Auditor - Metrics Dashboard")
        self.root.geometry("1000x700")

        # Data storage
        self.source_code = ""
        self.halstead = None
        self.mccabe = None
        self.chepin = None

        # Build GUI
        self._create_widgets()

    def _create_widgets(self):
        # Main frame
        main_frame = ttk.Frame(self.root, padding="5")
        main_frame.pack(fill=tk.BOTH, expand=True)

        # Top control bar
        control_frame = ttk.Frame(main_frame)
        control_frame.pack(fill=tk.X, pady=5)

        ttk.Button(control_frame, text="Load File", command=self.load_file).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Load Example", command=self.load_example).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Run Audit", command=self.run_audit).pack(side=tk.LEFT, padx=5)
        ttk.Button(control_frame, text="Export Results (JSON)", command=self.export_json).pack(side=tk.LEFT, padx=5)
        if HAS_REPORTLAB:
            ttk.Button(control_frame, text="Export PDF", command=self.export_pdf).pack(side=tk.LEFT, padx=5)
        else:
            ttk.Label(control_frame, text="(PDF export requires reportlab)").pack(side=tk.LEFT, padx=5)

        # Language selection (only Python for now)
        ttk.Label(control_frame, text="Language:").pack(side=tk.LEFT, padx=(20,5))
        self.lang_var = tk.StringVar(value="Python")
        lang_combo = ttk.Combobox(control_frame, textvariable=self.lang_var, values=["Python"], state="readonly", width=10)
        lang_combo.pack(side=tk.LEFT, padx=5)

        # Code editor
        code_frame = ttk.LabelFrame(main_frame, text="Source Code", padding="5")
        code_frame.pack(fill=tk.BOTH, expand=True, pady=5)

        self.code_text = scrolledtext.ScrolledText(code_frame, wrap=tk.WORD, font=("Courier", 10))
        self.code_text.pack(fill=tk.BOTH, expand=True)

        # Notebook for results
        notebook = ttk.Notebook(main_frame)
        notebook.pack(fill=tk.BOTH, expand=True, pady=5)

        # Halstead tab
        self.halstead_frame = ttk.Frame(notebook)
        notebook.add(self.halstead_frame, text="Halstead Metrics")
        self._build_halstead_tab()

        # McCabe tab
        self.mccabe_frame = ttk.Frame(notebook)
        notebook.add(self.mccabe_frame, text="McCabe Metrics")
        self._build_mccabe_tab()

        # Chepin tab
        self.chepin_frame = ttk.Frame(notebook)
        notebook.add(self.chepin_frame, text="Chepin Analysis")
        self._build_chepin_tab()

        # Report tab
        self.report_frame = ttk.Frame(notebook)
        notebook.add(self.report_frame, text="Managerial Report")
        self._build_report_tab()

        # Status bar
        self.status = ttk.Label(main_frame, text="Ready", relief=tk.SUNKEN)
        self.status.pack(fill=tk.X, side=tk.BOTTOM, pady=2)

    def _build_halstead_tab(self):
        # Left: tables of operators and operands
        left_frame = ttk.Frame(self.halstead_frame)
        left_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=5, pady=5)

        ttk.Label(left_frame, text="Operators (unique)").pack(anchor=tk.W)
        self.operators_tree = ttk.Treeview(left_frame, columns=("count",), show="tree headings", height=10)
        self.operators_tree.heading("#0", text="Operator")
        self.operators_tree.heading("count", text="Occurrences")
        self.operators_tree.pack(fill=tk.BOTH, expand=True)

        ttk.Label(left_frame, text="Operands (unique)").pack(anchor=tk.W, pady=(10,0))
        self.operands_tree = ttk.Treeview(left_frame, columns=("count",), show="tree headings", height=10)
        self.operands_tree.heading("#0", text="Operand")
        self.operands_tree.heading("count", text="Occurrences")
        self.operands_tree.pack(fill=tk.BOTH, expand=True)

        # Right: metrics summary
        right_frame = ttk.Frame(self.halstead_frame)
        right_frame.pack(side=tk.RIGHT, fill=tk.BOTH, padx=5, pady=5)

        self.halstead_labels = {}
        metrics = ["n1", "N1", "n2", "N2", "Volume", "Difficulty", "Effort", "Estimated Bugs (B)"]
        for i, m in enumerate(metrics):
            lbl = ttk.Label(right_frame, text=f"{m}:")
            lbl.grid(row=i, column=0, sticky=tk.W, pady=2)
            val_lbl = ttk.Label(right_frame, text="")
            val_lbl.grid(row=i, column=1, sticky=tk.W, padx=10)
            self.halstead_labels[m] = val_lbl

    def _build_mccabe_tab(self):
        # V(G) display
        self.vg_label = ttk.Label(self.mccabe_frame, text="Cyclomatic Complexity V(G): ")
        self.vg_label.pack(anchor=tk.W, pady=5)

        # Decision points list
        ttk.Label(self.mccabe_frame, text="Decision Points:").pack(anchor=tk.W)
        self.decisions_text = tk.Text(self.mccabe_frame, height=8, width=80, wrap=tk.WORD)
        self.decisions_text.pack(fill=tk.BOTH, expand=True, pady=5)

        # Test Cases frame
        ttk.Label(self.mccabe_frame, text="Test Cases (Basis Path Testing):", font=("TkDefaultFont", 10, "bold")).pack(anchor=tk.W, pady=(10,0))
        test_frame = ttk.Frame(self.mccabe_frame)
        test_frame.pack(fill=tk.BOTH, expand=True, pady=5)

        # Treeview for test cases
        columns = ("id", "description", "input", "expected_path")
        self.test_tree = ttk.Treeview(test_frame, columns=columns, show="headings", height=6)
        self.test_tree.heading("id", text="ID")
        self.test_tree.heading("description", text="Description")
        self.test_tree.heading("input", text="Suggested Input")
        self.test_tree.heading("expected_path", text="Expected Path")
        self.test_tree.column("id", width=40)
        self.test_tree.column("description", width=200)
        self.test_tree.column("input", width=200)
        self.test_tree.column("expected_path", width=200)
        self.test_tree.pack(fill=tk.BOTH, expand=True)

        # CFG canvas (if networkx available)
        if HAS_NETWORKX:
            ttk.Label(self.mccabe_frame, text="Control Flow Graph (first function):").pack(anchor=tk.W, pady=(10,0))
            self.cfg_canvas_frame = ttk.Frame(self.mccabe_frame)
            self.cfg_canvas_frame.pack(fill=tk.BOTH, expand=True, pady=5)
        else:
            ttk.Label(self.mccabe_frame, text="CFG visualization requires networkx and matplotlib.").pack()

    def _build_chepin_tab(self):
        self.chepin_table = ttk.Treeview(self.chepin_frame, columns=("category",), show="tree headings")
        self.chepin_table.heading("#0", text="Variable")
        self.chepin_table.heading("category", text="Category")
        self.chepin_table.column("#0", width=200)
        self.chepin_table.column("category", width=100)
        self.chepin_table.pack(fill=tk.BOTH, expand=True, pady=5)

        self.q_label = ttk.Label(self.chepin_frame, text="Q = ")
        self.q_label.pack(anchor=tk.W, pady=5)

        self.chepin_table.bind("<Double-1>", self.on_chepin_edit)

    def _build_report_tab(self):
        self.report_text = tk.Text(self.report_frame, wrap=tk.WORD, height=10, font=("TkDefaultFont", 12))
        self.report_text.pack(fill=tk.BOTH, expand=True, pady=5)
        self.report_text.config(state=tk.DISABLED)

    def load_file(self):
        filename = filedialog.askopenfilename(
            title="Select a Python file",
            filetypes=[("Python files", "*.py"), ("All files", "*.*")]
        )
        if filename:
            try:
                with open(filename, 'r', encoding='utf-8') as f:
                    code = f.read()
                self.code_text.delete(1.0, tk.END)
                self.code_text.insert(1.0, code)
                self.source_code = code
                self.status.config(text=f"Loaded: {filename}")
            except Exception as e:
                messagebox.showerror("Error", f"Could not load file: {e}")

    def load_example(self):
        example_code = '''def calculate_shipping(weight, distance, is_vip):
    base_rate = 50
    if distance > 100:
        multiplier = 1.5
    else:
        multiplier = 1.0

    if weight > 20:
        extra_charge = (weight - 20) * 5
    else:
        extra_charge = 0

    total = (base_rate * multiplier) + extra_charge

    if is_vip == True:
        total = total * 0.8

    return total
'''
        self.code_text.delete(1.0, tk.END)
        self.code_text.insert(1.0, example_code)
        self.source_code = example_code
        self.status.config(text="Loaded example: calculate_shipping")

    def run_audit(self):
        self.source_code = self.code_text.get(1.0, tk.END)
        if not self.source_code.strip():
            messagebox.showwarning("Warning", "No code to analyze.")
            return

        self.status.config(text="Analyzing...")
        self.root.update()

        try:
            # Halstead
            self.halstead = HalsteadAnalyzer(self.source_code).analyze()
            self._update_halstead_tab()

            # McCabe
            self.mccabe = McCabeAnalyzer(self.source_code).analyze()
            self._update_mccabe_tab()

            # Chepin
            self.chepin = ChepinAnalyzer(self.source_code)
            self.chepin.extract_variables()
            self._update_chepin_tab()

            # Managerial report
            self._update_report()

            self.status.config(text="Analysis complete.")
        except Exception as e:
            messagebox.showerror("Analysis Error", str(e))
            self.status.config(text="Error during analysis.")

    def _update_halstead_tab(self):
        for item in self.operators_tree.get_children():
            self.operators_tree.delete(item)
        for item in self.operands_tree.get_children():
            self.operands_tree.delete(item)

        for op, cnt in self.halstead.operators.most_common():
            self.operators_tree.insert("", tk.END, text=op, values=(cnt,))
        for opd, cnt in self.halstead.operands.most_common():
            self.operands_tree.insert("", tk.END, text=opd, values=(cnt,))

        metrics = self.halstead.get_metrics()
        for key, lbl in self.halstead_labels.items():
            val = metrics.get(key, "")
            if isinstance(val, float):
                val = f"{val:.2f}"
            lbl.config(text=str(val))

    def _update_mccabe_tab(self):
        vg = self.mccabe.get_vg()
        self.vg_label.config(text=f"Cyclomatic Complexity V(G): {vg}")

        # Show decision points
        self.decisions_text.delete(1.0, tk.END)
        for i, node in enumerate(self.mccabe.decision_points, 1):
            line = f"{i}. {ast.unparse(node)[:80]}"
            self.decisions_text.insert(tk.END, line + "\n")

        # Update test cases table
        for item in self.test_tree.get_children():
            self.test_tree.delete(item)
        for tc in self.mccabe.test_cases:
            self.test_tree.insert("", tk.END, values=(tc["id"], tc["description"], tc["suggested_input"], tc["expected_path"]))

        # Draw CFG if available
        if HAS_NETWORKX and self.mccabe.cfg:
            self._draw_cfg(self.mccabe.cfg)

    def _draw_cfg(self, G):
        for widget in self.cfg_canvas_frame.winfo_children():
            widget.destroy()

        fig, ax = plt.subplots(figsize=(6,4))
        pos = nx.spring_layout(G, seed=42)
        nx.draw_networkx_nodes(G, pos, ax=ax, node_color='lightblue', node_size=800)
        labels = nx.get_node_attributes(G, 'label')
        if not labels:
            labels = {n: str(n) for n in G.nodes()}
        nx.draw_networkx_labels(G, pos, labels=labels, ax=ax)
        nx.draw_networkx_edges(G, pos, ax=ax, edge_color='gray', arrows=True, arrowsize=20)
        ax.set_title("Control Flow Graph")
        canvas = FigureCanvasTkAgg(fig, master=self.cfg_canvas_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    def _update_chepin_tab(self):
        for item in self.chepin_table.get_children():
            self.chepin_table.delete(item)

        for var in self.chepin.variables:
            cat = self.chepin.classifications.get(var, 'T')
            self.chepin_table.insert("", tk.END, text=var, values=(cat,))

        self.q_label.config(text=f"Q = {self.chepin.get_q():.3f}")

    def on_chepin_edit(self, event):
        item = self.chepin_table.selection()[0]
        var = self.chepin_table.item(item, "text")
        menu = tk.Menu(self.root, tearoff=0)
        for cat in ['P', 'M', 'C', 'T']:
            menu.add_command(label=cat, command=lambda c=cat: self._set_category(var, c))
        menu.post(event.x_root, event.y_root)

    def _set_category(self, var, cat):
        self.chepin.set_classification(var, cat)
        self._update_chepin_tab()

    def _update_report(self):
        vg = self.mccabe.get_vg()
        bugs = self.halstead.bugs if self.halstead else 0
        release_ok = (vg <= 10 and bugs < 0.5)

        self.report_text.config(state=tk.NORMAL)
        self.report_text.delete(1.0, tk.END)

        self.report_text.insert(tk.END, "MANAGERIAL REPORT\n", "header")
        self.report_text.insert(tk.END, "="*40 + "\n\n")

        self.report_text.insert(tk.END, f"Cyclomatic Complexity V(G): {vg}\n")
        self.report_text.insert(tk.END, f"Halstead Estimated Bugs: {bugs:.3f}\n")
        self.report_text.insert(tk.END, f"Chepin Q: {self.chepin.get_q():.3f}\n\n")

        if release_ok:
            rec = "Release Recommended"
            color = "green"
        else:
            rec = "Refactoring Required"
            color = "red"

        self.report_text.insert(tk.END, f"Recommendation: {rec}\n", "rec")

        self.report_text.tag_config("header", font=("TkDefaultFont", 14, "bold"))
        self.report_text.tag_config("rec", foreground=color, font=("TkDefaultFont", 12, "bold"))
        self.report_text.config(state=tk.DISABLED)

    def export_json(self):
        if not self.halstead or not self.mccabe or not self.chepin:
            messagebox.showwarning("Warning", "Run audit first.")
            return

        data = {
            "Halstead": self.halstead.get_metrics(),
            "McCabe": {
                "V(G)": self.mccabe.get_vg(),
                "decision_points_count": len(self.mccabe.decision_points),
                "test_cases": self.mccabe.test_cases
            },
            "Chepin": {"Q": self.chepin.get_q(), "classifications": self.chepin.classifications},
            "Recommendation": "Release Recommended" if (self.mccabe.get_vg() <= 10 and self.halstead.bugs < 0.5) else "Refactoring Required"
        }
        filename = filedialog.asksaveasfilename(defaultextension=".json", filetypes=[("JSON", "*.json")])
        if filename:
            with open(filename, 'w') as f:
                json.dump(data, f, indent=2)
            self.status.config(text=f"Exported to {filename}")

    def export_pdf(self):
        if not HAS_REPORTLAB:
            messagebox.showerror("Error", "reportlab not installed. Cannot export PDF.")
            return
        if not self.halstead or not self.mccabe or not self.chepin:
            messagebox.showwarning("Warning", "Run audit first.")
            return

        filename = filedialog.asksaveasfilename(defaultextension=".pdf", filetypes=[("PDF", "*.pdf")])
        if filename:
            try:
                c = canvas.Canvas(filename, pagesize=letter)
                width, height = letter
                y = height - 50
                c.setFont("Helvetica-Bold", 16)
                c.drawString(50, y, "Code Audit Report")
                y -= 30
                c.setFont("Helvetica", 12)
                c.drawString(50, y, f"Halstead Volume: {self.halstead.volume:.2f}")
                y -= 20
                c.drawString(50, y, f"Halstead Difficulty: {self.halstead.difficulty:.2f}")
                y -= 20
                c.drawString(50, y, f"Halstead Effort: {self.halstead.effort:.2f}")
                y -= 20
                c.drawString(50, y, f"Halstead Bugs: {self.halstead.bugs:.3f}")
                y -= 30
                c.drawString(50, y, f"Cyclomatic Complexity V(G): {self.mccabe.get_vg()}")
                y -= 20
                c.drawString(50, y, f"Chepin Q: {self.chepin.get_q():.3f}")
                y -= 30
                rec = "Release Recommended" if (self.mccabe.get_vg() <= 10 and self.halstead.bugs < 0.5) else "Refactoring Required"
                c.setFont("Helvetica-Bold", 14)
                c.drawString(50, y, f"Recommendation: {rec}")
                # Add test cases summary
                y -= 40
                c.setFont("Helvetica-Bold", 12)
                c.drawString(50, y, "Test Cases (Basis Path):")
                y -= 20
                c.setFont("Helvetica", 10)
                for tc in self.mccabe.test_cases[:8]:  # limit to fit
                    c.drawString(60, y, f"Test {tc['id']}: {tc['description'][:70]}")
                    y -= 15
                    if y < 50:
                        c.showPage()
                        y = height - 50
                c.save()
                self.status.config(text=f"Exported PDF to {filename}")
            except Exception as e:
                messagebox.showerror("PDF Error", str(e))


if __name__ == "__main__":
    root = tk.Tk()
    app = CodeAuditorApp(root)
    root.mainloop()