from typing import List, Dict, Set, Tuple, Optional
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext
class Rule:
    def __init__(self):
        self.left: List[str] = []
        self.right: List[str] = []
class Grammar:
    E = "e"
    chain_start = "<<"
    chain_end = ">>"
    def __init__(self):
        self.VN: Set[str] = set()
        self.VT: Set[str] = set()
        self.S: str = ""
        self.P: List[Rule] = []
        self.er: Set[str] = set()
    def is_regular(self) -> bool:
        for rule in self.P:
            if len(rule.left) != 1 or rule.left[0] not in self.VN:
                return False
            if len(rule.right) == 1:
                if rule.right[0] not in self.VT:
                    return False
            elif len(rule.right) == 2:
                if (rule.right[0] in self.VN and rule.right[1] in self.VN):
                    return False
                if (rule.right[0] in self.VT and rule.right[1] in self.VT):
                    return False
            else:
                return False

        return True
    def is_context_free(self) -> bool:
        for rule in self.P:
            if len(rule.left) != 1:
                return False
        return True
    def exists_language(self) -> bool:
        N0 = self.calc_nterm()
        return self.S in N0
    def calc_nterm(self) -> Set[str]:
        N0 = set()
        N1 = set()
        while True:
            for rule in self.P:
                ok = True
                for symbol in rule.right:
                    if symbol not in N0 and symbol not in self.VT:
                        ok = False
                        break
                if ok and rule.left:
                    N1.add(rule.left[0])
            if N0 == N1:
                break
            N0 = N1.copy()
        return N0
    def remove_unused(self):
        N = self.calc_nterm()
        U = self.VN - N
        self.VN = N
        self.delete_set(U)
    def remove_unattainable(self):
        d = set()
        r = set()
        u = set()
        d.add(self.S)
        while d:
            q = d.pop()
            for rule in self.P:
                if q not in rule.left:
                    continue
                for symbol in rule.right:
                    if self.is_terminal(symbol):
                        continue
                    if symbol not in r and symbol not in d:
                        d.add(symbol)
            r.add(q)
        u = self.VN - r
        self.VN = r
        self.delete_set(u)
    def delete_set(self, symbols: Set[str]):
        self.P = [rule for rule in self.P
                  if not any(s in rule.left or s in rule.right for s in symbols)]
        new_VT = set()
        for rule in self.P:
            for symbol in rule.left:
                if not self.is_non_terminal(symbol):
                    new_VT.add(symbol)
            for symbol in rule.right:
                if not self.is_non_terminal(symbol):
                    new_VT.add(symbol)
        self.VT = new_VT
    def remove_e_rules(self):
        d0 = set()
        d1 = set()
        for rule in self.P:
            if len(rule.right) == 1 and rule.right[0] == self.E:
                d0.add(rule.left[0])
        while True:
            d1 = d0.copy()
            for rule in self.P:
                if len(rule.left) != 1:
                    continue
                ok = True
                for symbol in rule.right:
                    if symbol not in d1 and not self.is_terminal(symbol):
                        ok = False
                        break
                if ok and rule.left:
                    d0.add(rule.left[0])
            if d1 == d0:
                break
        P2 = []
        for rule in self.P:
            if len(rule.right) == 1 and rule.right[0] == self.E:
                continue
            e_positions = [i for i, sym in enumerate(rule.right)
                           if sym in d0]
            if not e_positions:
                P2.append(rule)
                continue
            n = len(e_positions)
            for mask in range(1, 1 << n):
                new_rule = Rule()
                new_rule.left = rule.left.copy()
                e_idx = 0
                for i, sym in enumerate(rule.right):
                    if e_idx < n and i == e_positions[e_idx]:
                        if mask & (1 << (n - 1 - e_idx)):
                            new_rule.right.append(sym)
                        e_idx += 1
                    else:
                        new_rule.right.append(sym)
                if new_rule.right:
                    P2.append(new_rule)
        if self.S in d0:
            new_start = self.next_non_terminal()
            new_rule1 = Rule()
            new_rule1.left = [new_start]
            new_rule1.right = [self.S]
            new_rule2 = Rule()
            new_rule2.left = [new_start]
            new_rule2.right = [self.E]
            P2.extend([new_rule1, new_rule2])
            self.S = new_start
            self.VN.add(new_start)
        self.P = P2
    def next_non_terminal(self) -> str:
        for c in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ':
            if c not in self.VN:
                return c
        return 'Z'
    def remove_chain_rules(self):
        N = {}
        for A in self.VN:
            N0 = {A}
            N1 = set()

            while True:
                N1 = N0.copy()
                for rule in self.P:
                    if (len(rule.left) == 1 and rule.left[0] in N0 and
                            len(rule.right) == 1 and self.is_non_terminal(rule.right[0])):
                        N0.add(rule.right[0])

                if N1 == N0:
                    break

            N[A] = N0
        P2 = []
        for rule in self.P:
            if (len(rule.right) == 1 and
                    self.is_non_terminal(rule.right[0])):
                continue
            A = rule.left[0]
            new_rule = Rule()
            new_rule.right = rule.right.copy()
            for nt in N:
                if A in N[nt]:
                    new_rule.left = [nt]
                    P2.append(new_rule)
        self.P = P2
        self.remove_unattainable()
    def remove_left_factor(self):
        changed = True

        while changed:
            changed = False

            for A in self.VN:
                rules = [rule for rule in self.P
                         if len(rule.left) == 1 and rule.left[0] == A and len(rule.right) > 1]
                if len(rules) < 2:
                    continue
                found = False
                for i in range(len(rules)):
                    if found:
                        break
                    for j in range(i + 1, len(rules)):
                        prefix = []
                        min_len = min(len(rules[i].right), len(rules[j].right))
                        for k in range(min_len):
                            if rules[i].right[k] != rules[j].right[k]:
                                break
                            prefix.append(rules[i].right[k])
                        if len(prefix) >= 2:
                            new_nt = self.next_non_terminal()
                            self.VN.add(new_nt)
                            to_remove = []
                            new_rules = []

                            for rule in self.P:
                                if (len(rule.left) == 1 and rule.left[0] == A and
                                        len(rule.right) >= len(prefix) and
                                        rule.right[:len(prefix)] == prefix):
                                    new_rule = Rule()
                                    new_rule.left = [new_nt]
                                    new_rule.right = rule.right[len(prefix):]
                                    if new_rule.right:
                                        new_rules.append(new_rule)
                                    to_remove.append(rule)
                            for rule in to_remove:
                                self.P.remove(rule)
                            self.P.extend(new_rules)
                            factored_rule = Rule()
                            factored_rule.left = [A]
                            factored_rule.right = prefix + [new_nt]
                            self.P.append(factored_rule)
                            changed = True
                            found = True
                            break
    def remove_left_recursion(self):
        for A in list(self.VN):
            recursive_rules = []
            non_recursive_rules = []
            for rule in self.P:
                if len(rule.left) == 1 and rule.left[0] == A:
                    if len(rule.right) > 0 and rule.right[0] == A:
                        recursive_rules.append(rule)
                    else:
                        non_recursive_rules.append(rule)
            if not recursive_rules:
                continue
            new_nt = self.next_non_terminal()
            self.VN.add(new_nt)
            for rule in recursive_rules:
                rule.left = [new_nt]
                rule.right = rule.right[1:] + [new_nt]
            for rule in non_recursive_rules:
                new_rule = Rule()
                new_rule.left = rule.left.copy()
                new_rule.right = rule.right.copy() + [new_nt]
                self.P.append(new_rule)
            epsilon_rule = Rule()
            epsilon_rule.left = [new_nt]
            epsilon_rule.right = [self.E]
            self.P.append(epsilon_rule)
    def load(self, lines: List[str]) -> bool:
        self.VN.clear()
        self.VT.clear()
        self.P.clear()
        mode = 0
        for line in lines:
            line = self.trim(line)
            if mode == 1:
                arrow_pos = line.find("->")
                if arrow_pos != -1:
                    rule = Rule()
                    left_part = line[:arrow_pos].strip()
                    right_part = line[arrow_pos + 2:].strip()

                    rule.left = list(left_part)
                    rule.right = list(right_part)
                    self.P.append(rule)
                    continue
                mode = 0
            if line.lower().startswith("nonterminals"):
                parts = line.split(":")
                if len(parts) < 2:
                    continue
                symbols = self.trim(parts[1]).split()
                self.VN.update(symbols)
            elif line.lower().startswith("terminals"):
                parts = line.split(":")
                if len(parts) < 2:
                    continue
                symbols = self.trim(parts[1]).split()
                self.VT.update(symbols)
            elif line.lower().startswith("starting symbol"):
                parts = line.split(":")
                if len(parts) < 2:
                    continue
                self.S = self.trim(parts[1])
            elif line.lower().startswith("rules"):
                mode = 1
        return True
    @staticmethod
    def trim(s: str) -> str:
        return s.strip()
    def to_string(self) -> List[str]:
        lines = []
        lines.append(f"Nonterminals [{len(self.VN)}]: " + " ".join(sorted(self.VN)))
        lines.append(f"Terminals [{len(self.VT)}]: " + " ".join(sorted(self.VT)))
        lines.append(f"Rules [{len(self.P)}]:")
        sorted_rules = sorted(self.P, key=lambda r: (
            r.left[0] if r.left else "",
            -len(r.right),
            r.right[0] if r.right else ""
        ))

        for rule in sorted_rules:
            left = "".join(rule.left)
            right = "".join(rule.right)
            lines.append(f"   {left} -> {right}")

        lines.append(f"Starting symbol: {self.S}")
        return lines
    def print(self):
        for line in self.to_string():
            print(line)
    def is_non_terminal(self, symbol: str) -> bool:
        return symbol in self.VN
    def is_terminal(self, symbol: str) -> bool:
        return symbol in self.VT
    def clone(self, other):
        self.VN = other.VN.copy()
        self.VT = other.VT.copy()
        self.S = other.S
        self.P = [Rule() for _ in other.P]
        for i, rule in enumerate(other.P):
            self.P[i].left = rule.left.copy()
            self.P[i].right = rule.right.copy()
    def first1(self) -> Dict[str, Set[str]]:
        first = {nt: set() for nt in self.VN}
        changed = True
        for rule in self.P:
            if rule.left and rule.right:
                first[rule.left[0]].add(rule.right[0])
        while changed:
            changed = False
            first_copy = {k: v.copy() for k, v in first.items()}

            for nt in self.VN:
                to_add = set()
                for sym in first[nt]:
                    if sym in first:
                        to_add.update(first[sym])
                if to_add - first[nt]:
                    first[nt].update(to_add)
                    changed = True
            if first == first_copy:
                break
        for nt in first:
            first[nt] = {sym for sym in first[nt] if sym not in self.VN}
        return first
    def follow1(self) -> Dict[str, Set[str]]:
        first = self.first1()
        follow = {nt: set() for nt in self.VN}
        changed = True
        for rule in self.P:
            for i in range(len(rule.right) - 1):
                B = rule.right[i]
                if not self.is_non_terminal(B):
                    continue

                next_sym = rule.right[i + 1]
                follow[B].add(next_sym)
        follow[self.S].add(self.chain_end)
        while changed:
            changed = False
            follow_copy = {k: v.copy() for k, v in follow.items()}
            for rule in self.P:
                if not rule.right:
                    continue
                last_sym = rule.right[-1]
                if self.is_non_terminal(last_sym):
                    A = rule.left[0]
                    follow[last_sym].update(follow[A])
            for rule in self.P:
                for i in range(len(rule.right) - 1):
                    B = rule.right[i]
                    if not self.is_non_terminal(B):
                        continue
                    remaining = rule.right[i + 1:]
                    can_derive_epsilon = True
                    for sym in remaining:
                        if sym != self.E and (sym not in self.er or sym not in self.VN):
                            can_derive_epsilon = False
                            break
                    if can_derive_epsilon:
                        A = rule.left[0]
                        follow[B].update(follow[A])
            for rule in self.P:
                if not rule.right:
                    continue
                last_sym = rule.right[-1]
                if (self.is_non_terminal(last_sym) and
                        (last_sym in self.er or last_sym == self.E)):
                    A = rule.left[0]
                    follow[last_sym].update(follow[A])
            for nt in follow:
                if follow[nt] != follow_copy[nt]:
                    changed = True
                    break
        for nt in follow:
            follow[nt] = {sym for sym in follow[nt] if sym not in self.VN}

        return follow
    def is_ll1(self) -> bool:
        first = self.first1()
        follow = self.follow1()
        self.e_rules()
        alternatives = {}
        for rule in self.P:
            if rule.left:
                nt = rule.left[0]
                if rule.right:
                    first_sym = rule.right[0]
                    alternatives.setdefault(nt, set()).add(first_sym)
        for nt, syms in alternatives.items():
            if len(syms) <= 1 and nt not in self.er:
                continue
            first_sets = []
            for sym in syms:
                if sym in first:
                    first_sets.append(first[sym])
                else:
                    first_sets.append({sym})
            for i in range(len(first_sets)):
                for j in range(i + 1, len(first_sets)):
                    if first_sets[i] & first_sets[j]:
                        return False
            if nt in self.er:
                for sym in syms:
                    if sym == self.E:
                        continue
                    if sym in first:
                        if first[sym] & follow[nt]:
                            return False
                    else:
                        if sym in follow[nt]:
                            return False

        return True
    def e_rules(self):
        self.er.clear()
        for rule in self.P:
            if len(rule.right) == 1 and rule.right[0] == self.E:
                self.er.add(rule.left[0])
    def resolve(self, chain: str, trace: Optional[List[str]] = None) -> bool:
        if trace is not None:
            trace.clear()
        first = self.first1()
        follow = self.follow1()
        self.e_rules()
        rule_first = {}
        for rule in self.P:
            if rule.right:
                first_sym = rule.right[0]
                if first_sym in first:
                    rule_first[tuple(rule.right)] = first[first_sym].copy()
                else:
                    rule_first[tuple(rule.right)] = {first_sym}
        trace_line = ""
        stack = [self.S]
        pos = 0

        while True:
            if pos >= len(chain):
                a = self.E
            else:
                a = chain[pos]
            if not stack:
                X = self.E
            else:
                X = stack[-1]
            if trace is not None:
                stack_str = "".join(reversed(stack))
                remaining_input = chain[pos:] if pos < len(chain) else ""
                trace_line = f"{stack_str}\t{remaining_input}\t"

            if self.is_non_terminal(X):
                found_rule = None
                for rule in self.P:
                    if not rule.left or rule.left[0] != X:
                        continue
                    if not rule.right:
                        continue

                    first_set = rule_first.get(tuple(rule.right), set())
                    if a in first_set:
                        found_rule = rule
                        break

                if found_rule is None:
                    if a in follow.get(X, set()):
                        found_rule = Rule()
                        found_rule.left = [X]
                        found_rule.right = [self.E]

                if found_rule is None:
                    if trace is not None:
                        trace.append(trace_line)
                    return False

                # Generate trace
                if trace is not None:
                    left = "".join(found_rule.left)
                    right = "".join(found_rule.right)
                    trace_line += f"{left} -> {right}"
                    trace.append(trace_line)
                stack.pop()
                for sym in reversed(found_rule.right):
                    if sym != self.E:
                        stack.append(sym)

            else:
                if not stack and pos >= len(chain):
                    break

                if X == a:
                    if trace is not None:
                        trace_line += f"match {X}"
                        trace.append(trace_line)

                    stack.pop()
                    pos += 1
                else:
                    if trace is not None:
                        trace.append(trace_line)
                    return False

        return True
    def lr_sets(self) -> Tuple[Dict[str, Set[str]], Dict[str, Set[str]]]:
        L = {nt: set() for nt in self.VN}
        R = {nt: set() for nt in self.VN}
        for rule in self.P:
            if rule.left and rule.right:
                L[rule.left[0]].add(rule.right[0])
                R[rule.left[0]].add(rule.right[-1])
        changed = True
        while changed:
            changed = False
            L_copy = {k: v.copy() for k, v in L.items()}
            R_copy = {k: v.copy() for k, v in R.items()}
            for nt in self.VN:
                to_add = set()
                for sym in L[nt]:
                    if self.is_non_terminal(sym):
                        to_add.update(L_copy[sym])
                if to_add - L[nt]:
                    L[nt].update(to_add)
                    changed = True
            for nt in self.VN:
                to_add = set()
                for sym in R[nt]:
                    if self.is_non_terminal(sym):
                        to_add.update(R_copy[sym])
                if to_add - R[nt]:
                    R[nt].update(to_add)
                    changed = True
        return L, R
    def build_precedence_matrix(self, L: Dict[str, Set[str]], R: Dict[str, Set[str]]) -> Optional[Dict[Tuple[str, str], int]]:
        M = {}
        for rule in self.P:
            right = rule.right
            for i in range(1, len(right)):
                X = right[i]
                if not self.is_non_terminal(X):
                    continue
                Y = right[i - 1]
                for a in L.get(X, set()):
                    key = (Y, a)
                    if key in M and M[key] != -1:
                        return None
                    M[key] = -1
            for i in range(len(right) - 1, 0, -1):
                X = right[i - 1]
                if not self.is_non_terminal(X):
                    continue
                Y = right[i]
                for a in R.get(X, set()):
                    key = (a, Y)
                    if key in M and M[key] != 1:
                        return None
                    M[key] = 1
        for a in L.get(self.S, set()):
            key = (self.chain_start, a)
            if key in M and M[key] != -1:
                return None
            M[key] = -1
        for a in R.get(self.S, set()):
            key = (a, self.chain_end)
            if key in M and M[key] != 1:
                return None
            M[key] = 1
        for rule in self.P:
            if len(rule.right) < 2:
                continue
            for i in range(len(rule.right) - 1):
                X = rule.right[i]
                Y = rule.right[i + 1]
                key = (X, Y)
                if key in M and M[key] != 0:
                    return None
                M[key] = 0
        return M
    def resolve_sp(self, chain: str, trace: Optional[List[str]] = None) -> bool:
        if trace is not None:
            trace.clear()
        trace_line = ""
        L, R = self.lr_sets()
        M = self.build_precedence_matrix(L, R)
        if M is None:
            return False
        stack = [self.chain_start]
        pos = 0
        while True:
            if pos >= len(chain):
                a = self.chain_end
            else:
                a = chain[pos]
            X = self.find_handle_end(stack)
            if trace is not None:
                stack_str = "".join(stack[1:])
                remaining_input = chain[pos:] if pos < len(chain) else ""
                trace_line = f"{stack_str}\t{remaining_input}\t"
            key = (X, a)
            if key not in M:
                if (len(stack) == 2 and stack[0] == self.chain_start and
                        stack[1] == self.S and a == self.chain_end):
                    if trace is not None:
                        trace.append(trace_line)
                    return True
                if trace is not None:
                    trace.append(trace_line)
                return False
            relation = M[key]
            if relation <= 0:
                if trace is not None:
                    trace_line += "shift"
                    trace.append(trace_line)
                stack.append(a)
                pos += 1
            else:
                handle_start = self.find_handle_start(stack, M)
                if handle_start < 0:
                    if trace is not None:
                        trace.append(trace_line)
                    return False
                handle = stack[handle_start:]
                found_rule = None
                for rule in self.P:
                    if rule.right == handle:
                        found_rule = rule
                        break
                if found_rule is None:
                    if trace is not None:
                        trace.append(trace_line)
                    return False
                if trace is not None:
                    left = "".join(found_rule.left)
                    right = "".join(found_rule.right)
                    trace_line += f"{left} -> {right}"
                    trace.append(trace_line)
                del stack[handle_start:]
                stack.extend(found_rule.left)
    def find_handle_end(self, stack: List[str]) -> str:
        for sym in reversed(stack):
            if sym != self.chain_start:
                return sym
        return self.chain_start
    def find_handle_start(self, stack: List[str], M: Dict[Tuple[str, str], int]) -> int:
        if len(stack) < 2:
            return -1
        i = len(stack) - 2
        while i > 0:
            X = stack[i]
            Y = stack[i + 1]
            if (X, Y) in M and M[(X, Y)] == -1:
                return i + 1
            i -= 1
        return 1
class GrammarRecognizerApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Распознаватель цепочек для грамматики простого предшествования")
        self.geometry("880x505")
        self.grammar = Grammar()
        self.create_widgets()
        self.load_sample_grammar()
    def create_widgets(self):
        self.toolbar = ttk.Frame(self)
        self.toolbar.pack(side=tk.TOP, fill=tk.X)
        self.load_btn = ttk.Button(self.toolbar, text="Прочитать грамматику", command=self.load_grammar)
        self.load_btn.pack(side=tk.LEFT)
        self.calc_lr_btn = ttk.Button(self.toolbar, text="Рассчитать L и R",command=self.calculate_lr, state=tk.DISABLED)
        self.calc_lr_btn.pack(side=tk.LEFT)
        self.matrix_btn = ttk.Button(self.toolbar, text="Построить матрицу",command=self.build_matrix, state=tk.DISABLED)
        self.matrix_btn.pack(side=tk.LEFT)
        self.recognize_btn = ttk.Button(self.toolbar, text="Распознать цепочки",command=self.recognize_chain, state=tk.DISABLED)
        self.recognize_btn.pack(side=tk.LEFT)
        self.main_container = tk.PanedWindow(self, orient=tk.HORIZONTAL)
        self.main_container.pack(fill=tk.BOTH, expand=True)
        self.grammar_input = scrolledtext.ScrolledText(self.main_container, width=40, wrap=tk.NONE)
        self.main_container.add(self.grammar_input)
        self.right_panel = tk.PanedWindow(self.main_container, orient=tk.VERTICAL)
        self.main_container.add(self.right_panel)
        self.chain_frame = ttk.Frame(self.right_panel)
        self.right_panel.add(self.chain_frame)
        self.chain_label = ttk.Label(self.chain_frame, text="Введите цепочку:")
        self.chain_label.pack(side=tk.LEFT)
        self.chain_entry = ttk.Entry(self.chain_frame, width=50)
        self.chain_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self.chain_entry.insert(0, "acabab")
        self.output_text = scrolledtext.ScrolledText(self.right_panel, wrap=tk.WORD)
        self.right_panel.add(self.output_text)
    def load_sample_grammar(self):
        sample_grammar = """Nonterminals [4]: S A
Terminals [2]: a b c
Rules [11]:
   S -> Aab
   A -> aS
   A -> c
Starting symbol: S"""
        self.grammar_input.insert(tk.END, sample_grammar)
    def load_grammar(self):
        lines = self.grammar_input.get("1.0", tk.END).splitlines()
        if not self.grammar.load(lines):
            messagebox.showerror("Ошибка", "Не удалось считать грамматику")
            return
        self.output_text.insert(tk.END, "Заданная грамматика считана успешно\n")
        self.calc_lr_btn.config(state=tk.NORMAL)
    def calculate_lr(self):
        L, R = self.grammar.lr_sets()
        self.output_text.insert(tk.END, "\nL(A):\n")
        for nt, symbols in L.items():
            self.output_text.insert(tk.END, f"{nt}: {' '.join(symbols)}\n")
        self.output_text.insert(tk.END, "\nR(A):\n")
        for nt, symbols in R.items():
            self.output_text.insert(tk.END, f"{nt}: {' '.join(symbols)}\n")
        self.matrix_btn.config(state=tk.NORMAL)
    def build_matrix(self):
        L, R = self.grammar.lr_sets()
        M = self.grammar.build_precedence_matrix(L, R)
        if M is None:
            messagebox.showerror("Ошибка", "Грамматика не является грамматикой простого предшествования")
            return
        symbols = list(self.grammar.VN.union(self.grammar.VT))
        symbols.append(self.grammar.chain_end)
        self.output_text.insert(tk.END, "\nМатрица предшествования:\n")
        header = "     " + " ".join([s if s != self.grammar.chain_end else "Кн" for s in symbols])
        self.output_text.insert(tk.END, header + "\n")
        self.output_text.insert(tk.END, "-----" + "-" * (len(header) - 5) + "\n")
        row_symbols = list(self.grammar.VN.union(self.grammar.VT))
        row_symbols.append(self.grammar.chain_start)
        for row_sym in row_symbols:
            row_label = "Нч | " if row_sym == self.grammar.chain_start else f"{row_sym}  | "
            row = row_label
            for col_sym in symbols:
                key = (row_sym, col_sym)
                if key in M:
                    if M[key] == -1:
                        row += "< "
                    elif M[key] == 0:
                        row += "= "
                    elif M[key] == 1:
                        row += "> "
                else:
                    row += "  "
            self.output_text.insert(tk.END, row + "\n")
        self.recognize_btn.config(state=tk.NORMAL)
    def recognize_chain(self):
            chain = self.chain_entry.get()
            trace = []
            result = self.grammar.resolve_sp(chain, trace)
            self.output_text.insert(tk.END, f"\nЦепочка  '{chain}' is {'принадлежит ' if result else 'не принадлежит '}.\n")
            if trace:
                self.output_text.insert(tk.END, "\nШаги распознавания:\n")
                for step in trace:
                    self.output_text.insert(tk.END, step + "\n")
            self.output_text.see(tk.END)
if __name__ == "__main__":
    app = GrammarRecognizerApp()
    app.mainloop()