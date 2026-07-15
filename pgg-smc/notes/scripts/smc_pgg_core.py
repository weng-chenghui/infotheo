"""
SMC-PGG Core Library
====================
Core classes for demonstrating SMC-PGG computation examples:
- Permutation: compose, inverse, identity, cycle notation
- MonodromyGroup: generators, evaluate word, endpoint
- TraceMonoid: independence relation, trace equivalence, Foata normal form
- SMCPGGProtocol: share, compute, verify_security
"""

import random
import itertools
from collections import defaultdict
from typing import List, Tuple, Set, Dict, Optional, Callable


class Permutation:
    """A permutation on {0, 1, ..., n-1} stored as a list."""

    def __init__(self, perm: List[int]):
        self.perm = list(perm)
        self.n = len(perm)

    @staticmethod
    def identity(n: int) -> 'Permutation':
        return Permutation(list(range(n)))

    @staticmethod
    def from_cycles(n: int, *cycles: Tuple[int, ...]) -> 'Permutation':
        """Create permutation from cycle notation. E.g., from_cycles(5, (0,1,2,3,4))."""
        p = list(range(n))
        for cycle in cycles:
            for i in range(len(cycle)):
                p[cycle[i]] = cycle[(i + 1) % len(cycle)]
        return Permutation(p)

    @staticmethod
    def transposition(n: int, i: int, j: int) -> 'Permutation':
        p = list(range(n))
        p[i], p[j] = p[j], p[i]
        return Permutation(p)

    @staticmethod
    def random(n: int) -> 'Permutation':
        p = list(range(n))
        random.shuffle(p)
        return Permutation(p)

    def __call__(self, i: int) -> int:
        return self.perm[i]

    def compose(self, other: 'Permutation') -> 'Permutation':
        """self ∘ other: apply other first, then self."""
        assert self.n == other.n
        return Permutation([self.perm[other.perm[i]] for i in range(self.n)])

    def __mul__(self, other: 'Permutation') -> 'Permutation':
        """self * other = self ∘ other (left-to-right convention: apply self first, then other).
        For word products w = g1 · g2 · ... · gL, we want g1 * g2 * ... * gL
        to mean: apply g1 first, then g2, etc.
        So self * other = other ∘ self (other after self).
        """
        return other.compose(self)

    def inverse(self) -> 'Permutation':
        inv = [0] * self.n
        for i in range(self.n):
            inv[self.perm[i]] = i
        return Permutation(inv)

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Permutation):
            return NotImplemented
        return self.perm == other.perm

    def __hash__(self) -> int:
        return hash(tuple(self.perm))

    def __repr__(self) -> str:
        return self.cycle_notation()

    def is_identity(self) -> bool:
        return all(self.perm[i] == i for i in range(self.n))

    def cycle_notation(self) -> str:
        visited = [False] * self.n
        cycles = []
        for i in range(self.n):
            if visited[i] or self.perm[i] == i:
                visited[i] = True
                continue
            cycle = []
            j = i
            while not visited[j]:
                visited[j] = True
                cycle.append(j)
                j = self.perm[j]
            if len(cycle) > 1:
                cycles.append(tuple(cycle))
        if not cycles:
            return "()"
        return "".join(str(c) for c in cycles)

    def order(self) -> int:
        """Order of permutation (LCM of cycle lengths)."""
        from math import gcd
        visited = [False] * self.n
        lengths = []
        for i in range(self.n):
            if visited[i]:
                continue
            length = 0
            j = i
            while not visited[j]:
                visited[j] = True
                j = self.perm[j]
                length += 1
            lengths.append(length)
        result = 1
        for l in lengths:
            result = result * l // gcd(result, l)
        return result

    def commutes_with(self, other: 'Permutation') -> bool:
        return (self * other) == (other * self)


def word_product(factors: List[Permutation]) -> Permutation:
    """Compute product g1 * g2 * ... * gL (left-to-right application)."""
    if not factors:
        raise ValueError("Empty factor list")
    result = Permutation.identity(factors[0].n)
    for f in factors:
        result = result * f
    return result


def commutator(a: Permutation, b: Permutation) -> Permutation:
    """[a, b] = a^{-1} b^{-1} a b"""
    return a.inverse() * b.inverse() * a * b


class MonodromyGroup:
    """A monodromy group G ≤ S_N with named generators."""

    def __init__(self, n_sheets: int, generators: Dict[str, Permutation]):
        self.n_sheets = n_sheets
        self.generators = generators
        self.gen_names = list(generators.keys())

    def evaluate_word(self, word: List[str]) -> Permutation:
        """Evaluate a word (list of generator names) as a product in G."""
        result = Permutation.identity(self.n_sheets)
        for letter in word:
            if letter.startswith('-'):
                # Inverse generator
                result = result * self.generators[letter[1:]].inverse()
            else:
                result = result * self.generators[letter]
        return result

    def endpoint(self, word: List[str], start_sheet: int) -> int:
        """Compute endpoint(w, s) = eval(w)(s)."""
        g = self.evaluate_word(word)
        return g(start_sheet)

    def all_elements(self) -> Set[Permutation]:
        """Generate all group elements by closure (BFS)."""
        elements = {Permutation.identity(self.n_sheets)}
        queue = list(elements)
        while queue:
            g = queue.pop(0)
            for gen in self.generators.values():
                for h in [g * gen, g * gen.inverse()]:
                    if h not in elements:
                        elements.add(h)
                        queue.append(h)
        return elements

    def order(self) -> int:
        return len(self.all_elements())


class TraceMonoid:
    """Trace monoid M(Σ, I) with independence relation I."""

    def __init__(self, alphabet: List[str], independence: Set[Tuple[str, str]]):
        """
        alphabet: list of generator names
        independence: set of pairs (a, b) where a and b commute
        """
        self.alphabet = alphabet
        # Make independence symmetric
        self.independence = set()
        for a, b in independence:
            self.independence.add((a, b))
            self.independence.add((b, a))

    def are_independent(self, a: str, b: str) -> bool:
        return (a, b) in self.independence

    def trace_equivalent(self, w1: List[str], w2: List[str]) -> bool:
        """Check if w1 ~_I w2 by reducing both to Foata normal form."""
        return self.foata_normal_form(w1) == self.foata_normal_form(w2)

    def foata_normal_form(self, word: List[str]) -> List[Tuple[str, ...]]:
        """
        Compute the Foata normal form: a sequence of "blocks" where
        each block is a maximal antichain (set of pairwise independent letters)
        that can fire simultaneously.
        """
        if not word:
            return []

        # Build dependency graph: position i depends on position j (j < i)
        # if word[i] and word[j] are NOT independent (they don't commute)
        # and j is the latest such position before i.
        n = len(word)
        # For each position, compute the "level" (which Foata block it belongs to)
        level = [0] * n
        for i in range(n):
            max_dep_level = -1
            for j in range(i - 1, -1, -1):
                if not self.are_independent(word[i], word[j]):
                    max_dep_level = max(max_dep_level, level[j])
            level[i] = max_dep_level + 1

        # Group by level
        num_levels = max(level) + 1 if level else 0
        blocks = [[] for _ in range(num_levels)]
        for i in range(n):
            blocks[level[i]].append(word[i])

        # Sort within each block for canonical form
        return [tuple(sorted(block)) for block in blocks]

    def foata_depth(self, word: List[str]) -> int:
        """Number of Foata blocks = parallel execution rounds."""
        fnf = self.foata_normal_form(word)
        return len(fnf)


class SMCPGGProtocol:
    """SMC-PGG protocol: share, compute, verify security."""

    def __init__(self, monodromy: MonodromyGroup):
        self.monodromy = monodromy

    def share(self, secret_word: List[str], num_parties: int) -> List[List[str]]:
        """
        Split a word into num_parties sub-words whose concatenation = secret_word.
        Each sub-word is a contiguous segment (round-robin assignment).
        """
        shares = [[] for _ in range(num_parties)]
        for i, letter in enumerate(secret_word):
            shares[i % num_parties].append(letter)
        return shares

    def share_random(self, secret_element: Permutation, num_parties: int,
                     word_length: int = 10) -> List[List[str]]:
        """
        Share a group element by generating a random word that evaluates to it.
        Generate (num_parties - 1) random sub-words, then compute the last one
        so the product equals the secret.
        """
        n = self.monodromy.n_sheets
        gen_names = self.monodromy.gen_names

        # Generate random prefixes for parties 0..num_parties-2
        shares = []
        prefix_product = Permutation.identity(n)
        for p in range(num_parties - 1):
            sub_len = max(1, word_length // num_parties)
            sub_word = [random.choice(gen_names) for _ in range(sub_len)]
            shares.append(sub_word)
            prefix_product = prefix_product * self.monodromy.evaluate_word(sub_word)

        # Last party's share: need prefix_product * last_eval = secret_element
        # So last_eval = prefix_product^{-1} * secret_element
        needed = prefix_product.inverse() * secret_element  # as permutation product

        # Express 'needed' as a word (brute force for small groups)
        last_word = self._express_as_word(needed)
        shares.append(last_word)
        return shares

    def _express_as_word(self, target: Permutation, max_len: int = 20) -> List[str]:
        """Find a word that evaluates to target (BFS)."""
        if target.is_identity():
            return []

        gen_names = self.monodromy.gen_names
        gens = self.monodromy.generators

        # BFS
        visited = {Permutation.identity(self.monodromy.n_sheets): []}
        queue = [(Permutation.identity(self.monodromy.n_sheets), [])]

        while queue:
            current, word = queue.pop(0)
            if len(word) >= max_len:
                continue
            for name in gen_names:
                new_perm = current * gens[name]
                new_word = word + [name]
                if new_perm == target:
                    return new_word
                if new_perm not in visited:
                    visited[new_perm] = new_word
                    queue.append((new_perm, new_word))

                # Also try inverse
                new_perm_inv = current * gens[name].inverse()
                new_word_inv = word + ['-' + name]
                if new_perm_inv == target:
                    return new_word_inv
                if new_perm_inv not in visited:
                    visited[new_perm_inv] = new_word_inv
                    queue.append((new_perm_inv, new_word_inv))

        raise ValueError(f"Could not express {target} as a word of length ≤ {max_len}")

    def compute(self, shares: List[List[str]]) -> Permutation:
        """Reconstruct: concatenate all shares and evaluate."""
        full_word = []
        for share in shares:
            full_word.extend(share)
        return self.monodromy.evaluate_word(full_word)

    def verify_security(self, secret: Permutation, num_parties: int = 3,
                        trials: int = 1000) -> Dict:
        """
        Empirical security check: generate many sharings of the same secret,
        verify that individual shares look uniformly distributed.
        """
        all_elements = self.monodromy.all_elements()
        group_order = len(all_elements)

        # Count distribution of each party's sub-word evaluation
        party_distributions = [defaultdict(int) for _ in range(num_parties)]

        for _ in range(trials):
            shares = self.share_random(secret, num_parties, word_length=12)
            for p in range(num_parties):
                eval_p = self.monodromy.evaluate_word(shares[p])
                party_distributions[p][eval_p] += 1

        # Check uniformity: chi-squared-like measure
        results = {"correct_reconstruction": 0, "total_trials": trials}
        for p in range(num_parties):
            dist = party_distributions[p]
            expected = trials / group_order
            chi_sq = sum((count - expected) ** 2 / expected
                         for count in dist.values())
            # Add missing elements
            chi_sq += (group_order - len(dist)) * expected
            results[f"party_{p}_distinct_values"] = len(dist)
            results[f"party_{p}_chi_sq"] = round(chi_sq, 2)
            results[f"party_{p}_expected_chi_sq"] = round(group_order - 1, 2)

        # Verify reconstruction
        correct = 0
        for _ in range(min(trials, 100)):
            shares = self.share_random(secret, num_parties, word_length=12)
            if self.compute(shares) == secret:
                correct += 1
        results["correct_reconstruction"] = correct
        results["reconstruction_trials"] = min(trials, 100)

        return results


# ============================================================
# Barrington construction helpers
# ============================================================

def barrington_and(alpha: Permutation, beta: Permutation,
                   x1_perms: Tuple[Permutation, Permutation],
                   x2_perms: Tuple[Permutation, Permutation]) -> Callable:
    """
    Barrington's AND gate via commutator.
    [α^x1, β^x2] = id if x1=0 or x2=0; = [α, β] if x1=x2=1.

    Returns a function (x1, x2) -> Permutation.

    x1_perms = (perm_when_0, perm_when_1) = (id, alpha)
    x2_perms = (perm_when_0, perm_when_1) = (id, beta)
    """
    e = Permutation.identity(alpha.n)

    def evaluate(x1: int, x2: int) -> Permutation:
        a = alpha if x1 else e
        b = beta if x2 else e
        return commutator(a, b)

    return evaluate


def barrington_or(alpha: Permutation, beta: Permutation) -> Callable:
    """OR(x1, x2) = NOT(AND(NOT(x1), NOT(x2))) via De Morgan."""
    and_gate = barrington_and(alpha, beta,
                              (Permutation.identity(alpha.n), alpha),
                              (Permutation.identity(alpha.n), beta))
    target = commutator(alpha, beta)

    def evaluate(x1: int, x2: int) -> Permutation:
        # OR = NOT AND(NOT x1, NOT x2)
        # AND(NOT x1, NOT x2) = [α^(1-x1), β^(1-x2)]
        return commutator(
            alpha if (1 - x1) else Permutation.identity(alpha.n),
            beta if (1 - x2) else Permutation.identity(alpha.n)
        )

    return evaluate


# ============================================================
# Utility functions
# ============================================================

def print_separator(title: str):
    print(f"\n{'=' * 60}")
    print(f"  {title}")
    print(f"{'=' * 60}")


def print_truth_table(func: Callable, n_vars: int, var_names: List[str],
                      target: Optional[Permutation] = None):
    """Print truth table for a function mapping bit-tuples to permutations."""
    for bits in itertools.product([0, 1], repeat=n_vars):
        result = func(*bits)
        if target is not None:
            output = 1 if result == target else 0
            print(f"  {dict(zip(var_names, bits))} -> {result} {'= target' if output else '= id' if result.is_identity() else ''}")
        else:
            print(f"  {dict(zip(var_names, bits))} -> {result}")
