r"""
Colored Permutations

.. TODO::

    Much of the colored permutations (and element) class can be
    generalized to `G \wr S_n`
"""
import itertools
from random import choice

from sage.structure.element import MultiplicativeGroupElement
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.misc.inherit_comparison import InheritComparisonClasscallMetaclass
from sage.misc.cachefunc import cached_method
from sage.misc.misc_c import prod
from sage.misc.lazy_attribute import lazy_attribute
from sage.arith.functions import lcm

from sage.combinat.permutation import Permutations
from sage.combinat.free_module import CombinatorialFreeModule
from sage.combinat.specht_module import SpechtModule as SymGroupSpechtModule
from sage.modules.with_basis.subquotient import SubmoduleWithBasis, QuotientModuleWithBasis
from sage.modules.with_basis.representation import Representation_abstract
from sage.matrix.constructor import matrix, diagonal_matrix
from sage.rings.finite_rings.integer_mod_ring import IntegerModRing
from sage.rings.number_field.number_field import CyclotomicField
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.integer_ring import ZZ


class ColoredPermutation(MultiplicativeGroupElement):
    """
    A colored permutation.
    """

    def __init__(self, parent, colors, perm):
        """
        Initialize ``self``.

        TESTS::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: TestSuite(s1*s2*t).run()
        """
        self._colors = tuple(colors)
        self._perm = perm
        MultiplicativeGroupElement.__init__(self, parent=parent)

    def __hash__(self):
        r"""
        TESTS::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: for gen in s1,s2,t:
            ....:     assert hash(gen) ^^ hash(gen._colors) == hash(gen._perm)
        """
        return hash(self._perm) ^ hash(self._colors)

    def _repr_(self):
        """
        Return a string representation of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: s1*s2*t
            [[1, 0, 0], [3, 1, 2]]
        """
        return repr([list(self._colors), self._perm])

    def _latex_(self):
        r"""
        Return a latex representation of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: latex(s1*s2*t)
            [3_{1}, 1_{0}, 2_{0}]
        """
        ret = "["
        ret += ", ".join("{}_{{{}}}".format(x, c)
                         for c, x in zip(self._colors, self._perm))
        return ret + "]"

    def __len__(self):
        """
        Return the length of the one line form of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(2, 3)
            sage: s1,s2,t = C.gens()
            sage: len(s1)
            3
        """
        return len(self._perm)

    def _mul_(self, other):
        """
        Multiply ``self`` and ``other``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: s1*s2*s1 == s2*s1*s2
            True
        """
        colors = tuple(c + other._colors[val - 1]  # -1 for indexing
                       for c, val in zip(self._colors, self._perm))
        p = self._perm._left_to_right_multiply_on_right(other._perm)
        return self.__class__(self.parent(), colors, p)

    def __invert__(self):
        """
        Return the inverse of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: ~t  # indirect doctest
            [[0, 0, 3], [1, 2, 3]]
            sage: all(x * ~x == C.one() for x in C.gens())
            True
        """
        ip = ~self._perm
        return self.__class__(self.parent(),
                              tuple(-self._colors[i - 1] for i in ip),  # -1 for indexing
                              ip)

    def __eq__(self, other):
        """
        Check equality.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: s1*s2*s1 == s2*s1*s2
            True
            sage: t^4 == C.one()
            True
            sage: s1*s2 == s2*s1
            False
        """
        if not isinstance(other, ColoredPermutation):
            return False
        return (self.parent() is other.parent()
                and self._colors == other._colors
                and self._perm == other._perm)

    def __ne__(self, other):
        """
        Check inequality.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: s1*s2*s1 != s2*s1*s2
            False
            sage: s1*s2 != s2*s1
            True
        """
        return not self == other

    def __iter__(self):
        """
        Iterate over ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: x = s1*s2*t
            sage: list(x)
            [(1, 3), (0, 1), (0, 2)]
        """
        yield from zip(self._colors, self._perm)

    def one_line_form(self):
        """
        Return the one line form of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: x = s1*s2*t
            sage: x
            [[1, 0, 0], [3, 1, 2]]
            sage: x.one_line_form()
            [(1, 3), (0, 1), (0, 2)]
        """
        return list(self)

    def __getitem__(self, key):
        """
        Return the specified element in the one line form of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: x = s1*s2*t
            sage: x
            [[1, 0, 0], [3, 1, 2]]
            sage: x[1]
            (0, 1)
            sage: x[1:]
            [(0, 1), (0, 2)]
        """
        if isinstance(key, slice):
            return list(zip(self._colors[key], self._perm[key]))
        return (self._colors[key], self._perm[key])

    def colors(self):
        """
        Return the colors of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: x = s1*s2*t
            sage: x.colors()
            [1, 0, 0]
        """
        return list(self._colors)

    def permutation(self):
        """
        Return the permutation of ``self``.

        This is obtained by forgetting the colors.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: x = s1*s2*t
            sage: x.permutation()
            [3, 1, 2]
        """
        return self._perm

    def to_matrix(self):
        """
        Return a matrix of ``self``.

        The colors are mapped to roots of unity.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s1,s2,t = C.gens()
            sage: x = s1*s2*t*s2; x.one_line_form()
            [(1, 2), (0, 1), (0, 3)]
            sage: M = x.to_matrix(); M                                                  # needs sage.rings.number_field
            [    0     1     0]
            [zeta4     0     0]
            [    0     0     1]

        The matrix multiplication is in the *opposite* order::

            sage: M == s2.to_matrix()*t.to_matrix()*s2.to_matrix()*s1.to_matrix()       # needs sage.rings.number_field
            True
        """
        Cp = CyclotomicField(self.parent()._m)
        g = Cp.gen()
        D = diagonal_matrix(Cp, [g ** i for i in self._colors])
        return self._perm.to_matrix() * D

    def has_left_descent(self, i):
        r"""
        Return ``True`` if ``i`` is a left descent of ``self``.

        Let `p = ((s_1, \ldots s_n), \sigma)` be a colored permutation.
        We say `p` has a left `n`-descent if `s_n > 0`. If `i < n`, then
        we say `p` has a left `i`-descent if either

        - `s_i \neq 0, s_{i+1} = 0` and `\sigma_i < \sigma_{i+1}` or
        - `s_i = s_{i+1}` and `\sigma_i > \sigma_{i+1}`.

        This notion of a left `i`-descent is done in order to recursively
        construct `w(p) = \sigma_i w(\sigma_i^{-1} p)`, where `w(p)`
        denotes a reduced word of `p`.

        EXAMPLES::

            sage: C = ColoredPermutations(2, 4)
            sage: s1,s2,s3,s4 = C.gens()
            sage: x = s4*s1*s2*s3*s4
            sage: [x.has_left_descent(i) for i in C.index_set()]
            [True, False, False, True]

            sage: C = ColoredPermutations(1, 5)
            sage: s1,s2,s3,s4 = C.gens()
            sage: x = s4*s1*s2*s3*s4
            sage: [x.has_left_descent(i) for i in C.index_set()]
            [True, False, False, True]

            sage: C = ColoredPermutations(3, 3)
            sage: x = C([[2,1,0],[3,1,2]])
            sage: [x.has_left_descent(i) for i in C.index_set()]
            [False, True, False]

            sage: C = ColoredPermutations(4, 4)
            sage: x = C([[2,1,0,1],[3,2,4,1]])
            sage: [x.has_left_descent(i) for i in C.index_set()]
            [False, True, False, True]
        """
        if self.parent()._m == 1:
            return self._perm[i - 1] > self._perm[i]

        if i == self.parent()._n:
            return self._colors[-1] != 0
        if self._colors[i - 1] != 0:
            return self._colors[i] == 0 or self._perm[i - 1] < self._perm[i]
        return self._colors[i] == 0 and self._perm[i - 1] > self._perm[i]

    def reduced_word(self):
        r"""
        Return a word in the simple reflections to obtain ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(3, 3)
            sage: x = C([[2,1,0],[3,1,2]])
            sage: x.reduced_word()
            [2, 1, 3, 2, 1, 3, 3]

            sage: C = ColoredPermutations(4, 4)
            sage: x = C([[2,1,0,1],[3,2,4,1]])
            sage: x.reduced_word()
            [2, 1, 4, 3, 2, 1, 4, 3, 2, 4, 4, 3]

        TESTS::

            sage: C = ColoredPermutations(3, 3)
            sage: all(C.from_reduced_word(p.reduced_word()) == p for p in C)
            True
        """
        if self == self.parent().one():
            return []
        I = self.parent().index_set()
        sinv = self.parent()._inverse_simple_reflections()
        for i in I:
            if self.has_left_descent(i):
                return [i] + (sinv[i] * self).reduced_word()
        assert False, "BUG in reduced_word"

    def length(self):
        r"""
        Return the length of ``self`` in generating reflections.

        This is the minimal numbers of generating reflections needed
        to obtain ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(3, 3)
            sage: x = C([[2,1,0],[3,1,2]])
            sage: x.length()
            7

            sage: C = ColoredPermutations(4, 4)
            sage: x = C([[2,1,0,1],[3,2,4,1]])
            sage: x.length()
            12

        TESTS::

            sage: C = ColoredPermutations(3, 3)
            sage: d = [p.length() for p in C]
            sage: [d.count(i) for i in range(14)]
            [1, 3, 6, 10, 15, 20, 23, 24, 23, 19, 12, 5, 1, 0]
            sage: d = [p.length() for p in ReflectionGroup([3, 1, 3])] # optional - gap3
            sage: [d.count(i) for i in range(14)]                      # optional - gap3
            [1, 3, 6, 10, 15, 20, 23, 24, 23, 19, 12, 5, 1, 0]

            sage: C = ColoredPermutations(4, 3)
            sage: d = [p.length() for p in C]
            sage: [d.count(i) for i in range(17)]
            [1, 3, 6, 11, 18, 27, 36, 44, 50, 52, 49, 40, 27, 14, 5, 1, 0]
            sage: d = [p.length() for p in ReflectionGroup([4, 1, 3])] # optional - gap3
            sage: [d.count(i) for i in range(17)]                      # optional - gap3
            [1, 3, 6, 11, 18, 27, 36, 44, 50, 52, 49, 40, 27, 14, 5, 1, 0]

            sage: C = ColoredPermutations(3, 4)
            sage: d = [p.length() for p in C]
            sage: [d.count(i) for i in range(22)]
            [1, 4, 10, 20, 35, 56, 82, 112, 144, 174, 197,
             209, 209, 197, 173, 138, 96, 55, 24, 7, 1, 0]
            sage: d = [p.length() for p in ReflectionGroup([3, 1, 4])] # optional - gap3
            sage: [d.count(i) for i in range(22)]                      # optional - gap3
            [1, 4, 10, 20, 35, 56, 82, 112, 144, 174, 197,
             209, 209, 197, 173, 138, 96, 55, 24, 7, 1, 0]
        """
        return ZZ(len(self.reduced_word()))

# TODO: Parts of this should be put in the category of complex
# reflection groups


class ColoredPermutations(Parent, UniqueRepresentation):
    r"""
    The group of `m`-colored permutations on `\{1, 2, \ldots, n\}`.

    Let `S_n` be the symmetric group on `n` letters and `C_m` be the cyclic
    group of order `m`. The `m`-colored permutation group on `n` letters
    is given by `P_n^m = C_m \wr S_n`. This is also the complex reflection
    group `G(m, 1, n)`.

    We define our multiplication by

    .. MATH::

        ((s_1, \ldots s_n), \sigma) \cdot ((t_1, \ldots, t_n), \tau)
        = ((s_1 t_{\sigma(1)}, \ldots, s_n t_{\sigma(n)}), \tau \sigma).

    EXAMPLES::

        sage: C = ColoredPermutations(4, 3); C
        4-colored permutations of size 3
        sage: s1,s2,t = C.gens()
        sage: (s1, s2, t)
        ([[0, 0, 0], [2, 1, 3]], [[0, 0, 0], [1, 3, 2]], [[0, 0, 1], [1, 2, 3]])
        sage: s1*s2
        [[0, 0, 0], [3, 1, 2]]
        sage: s1*s2*s1 == s2*s1*s2
        True
        sage: t^4 == C.one()
        True
        sage: s2*t*s2
        [[0, 1, 0], [1, 2, 3]]

    We can also create a colored permutation by passing
    an iterable consisting of tuples consisting of ``(color, element)``::

        sage: x = C([(2,1), (3,3), (3,2)]); x
        [[2, 3, 3], [1, 3, 2]]

    or a list of colors and a permutation::

        sage: C([[3,3,1], [1,3,2]])
        [[3, 3, 1], [1, 3, 2]]
        sage: C(([3,3,1], [1,3,2]))
        [[3, 3, 1], [1, 3, 2]]

    There is also the natural lift from permutations::

        sage: P = Permutations(3)
        sage: C(P.an_element())
        [[0, 0, 0], [3, 1, 2]]


    A colored permutation::

        sage: C(C.an_element()) == C.an_element()
        True

    REFERENCES:

    - :wikipedia:`Generalized_symmetric_group`
    - :wikipedia:`Complex_reflection_group`
    """

    def __init__(self, m, n):
        """
        Initialize ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: TestSuite(C).run()
            sage: C = ColoredPermutations(2, 3)
            sage: TestSuite(C).run()
            sage: C = ColoredPermutations(1, 3)
            sage: TestSuite(C).run()
        """
        if m <= 0:
            raise ValueError("m must be a positive integer")
        self._m = ZZ(m)
        self._n = ZZ(n)
        self._C = IntegerModRing(self._m)
        self._P = Permutations(self._n)

        if self._m == 1 or self._m == 2:
            from sage.categories.finite_coxeter_groups import FiniteCoxeterGroups
            category = FiniteCoxeterGroups().Irreducible()
        else:
            from sage.categories.complex_reflection_groups import ComplexReflectionGroups
            category = ComplexReflectionGroups().Finite().Irreducible().WellGenerated()
        Parent.__init__(self, category=category)

    def _repr_(self):
        """
        Return a string representation of ``self``.

        EXAMPLES::

            sage: ColoredPermutations(4, 3)
            4-colored permutations of size 3
        """
        return "{}-colored permutations of size {}".format(self._m, self._n)

    @cached_method
    def index_set(self):
        """
        Return the index set of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(3, 4)
            sage: C.index_set()
            (1, 2, 3, 4)

            sage: C = ColoredPermutations(1, 4)
            sage: C.index_set()
            (1, 2, 3)

        TESTS::

            sage: S = SignedPermutations(4)
            sage: S.index_set()
            (1, 2, 3, 4)
        """
        n = self._n
        if self._m != 1:
            n += 1
        return tuple(range(1, n))

    def coxeter_matrix(self):
        """
        Return the Coxeter matrix of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(3, 4)
            sage: C.coxeter_matrix()                                                    # needs sage.modules
            [1 3 2 2]
            [3 1 3 2]
            [2 3 1 4]
            [2 2 4 1]

            sage: C = ColoredPermutations(1, 4)
            sage: C.coxeter_matrix()                                                    # needs sage.modules
            [1 3 2]
            [3 1 3]
            [2 3 1]

        TESTS::

            sage: S = SignedPermutations(4)
            sage: S.coxeter_matrix()                                                    # needs sage.modules
            [1 3 2 2]
            [3 1 3 2]
            [2 3 1 4]
            [2 2 4 1]
        """
        from sage.combinat.root_system.cartan_type import CartanType
        if self._m == 1:
            return CartanType(['A', self._n - 1]).coxeter_matrix()
        return CartanType(['B', self._n]).coxeter_matrix()

    @cached_method
    def one(self):
        """
        Return the identity element of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: C.one()
            [[0, 0, 0], [1, 2, 3]]
        """
        return self.element_class(self, [self._C.zero()] * self._n,
                                  self._P.identity())

    def random_element(self):
        """
        Return an element drawn uniformly at random.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: s = C.random_element(); s # random
            [[0, 2, 1], [2, 1, 3]]
            sage: s in C
            True
        """
        return self.element_class(self,
                                  [self._C.random_element()
                                   for _ in range(self._n)],
                                  self._P.random_element())

    def simple_reflection(self, i):
        r"""
        Return the ``i``-th simple reflection of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: C.gens()
            ([[0, 0, 0], [2, 1, 3]], [[0, 0, 0], [1, 3, 2]], [[0, 0, 1], [1, 2, 3]])
            sage: C.simple_reflection(2)
            [[0, 0, 0], [1, 3, 2]]
            sage: C.simple_reflection(3)
            [[0, 0, 1], [1, 2, 3]]

            sage: S = SignedPermutations(4)
            sage: S.simple_reflection(1)
            [2, 1, 3, 4]
            sage: S.simple_reflection(4)
            [1, 2, 3, -4]
        """
        if i not in self.index_set():
            raise ValueError("i must be in the index set")
        colors = [self._C.zero()] * self._n
        if i < self._n:
            p = list(range(1, self._n + 1))
            p[i - 1] = i + 1
            p[i] = i
            return self.element_class(self, colors, self._P(p))
        colors[-1] = self._C.one()
        return self.element_class(self, colors, self._P.identity())

    @cached_method
    def _inverse_simple_reflections(self):
        """
        Return the inverse of the simple reflections of ``self``.

        .. WARNING::

            This returns a ``dict`` that should not be mutated since
            the result is cached.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: C._inverse_simple_reflections()
            {1: [[0, 0, 0], [2, 1, 3]],
             2: [[0, 0, 0], [1, 3, 2]],
             3: [[0, 0, 3], [1, 2, 3]]}
        """
        s = self.simple_reflections()
        return {i: ~s[i] for i in self.index_set()}

    @cached_method
    def gens(self) -> tuple:
        """
        Return the generators of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: C.gens()
            ([[0, 0, 0], [2, 1, 3]],
             [[0, 0, 0], [1, 3, 2]],
             [[0, 0, 1], [1, 2, 3]])

            sage: S = SignedPermutations(4)
            sage: S.gens()
            ([2, 1, 3, 4], [1, 3, 2, 4], [1, 2, 4, 3], [1, 2, 3, -4])
        """
        return tuple(self.simple_reflection(i) for i in self.index_set())

    def matrix_group(self):
        """
        Return the matrix group corresponding to ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: C.matrix_group()                                                      # needs sage.modules
            Matrix group over Cyclotomic Field of order 4 and degree 2 with 3 generators (
            [0 1 0]  [1 0 0]  [    1     0     0]
            [1 0 0]  [0 0 1]  [    0     1     0]
            [0 0 1], [0 1 0], [    0     0 zeta4]
            )
        """
        from sage.groups.matrix_gps.finitely_generated import MatrixGroup
        return MatrixGroup([g.to_matrix() for g in self.gens()])

    def as_permutation_group(self):
        r"""
        Return the permutation group corresponding to ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: C.as_permutation_group()                                              # needs sage.groups
            Complex reflection group G(4, 1, 3) as a permutation group
        """
        from sage.groups.perm_gps.permgroup_named import ComplexReflectionGroup
        return ComplexReflectionGroup(self._m, 1, self._n)

    def _element_constructor_(self, x):
        """
        Construct an element of ``self`` from ``x``.

        INPUT:

        Either a list of pairs (color, element)
        or a pair of lists (colors, elements).

        TESTS::

            sage: C = ColoredPermutations(4, 3)
            sage: x = C([(2,1), (3,3), (3,2)]); x
            [[2, 3, 3], [1, 3, 2]]
            sage: x == C([[2,3,3], [1,3,2]])
            True
        """
        if isinstance(x, self.element_class) and x.parent() is self:
            return self
        x = list(x)
        if isinstance(x[0], tuple):
            c = []
            p = []
            for k in x:
                if len(k) != 2:
                    raise ValueError("input must be pairs (color, element)")
                c.append(self._C(k[0]))
                p.append(k[1])
            return self.element_class(self, c, self._P(p))

        if len(x) != 2:
            raise ValueError("input must be a pair of a list of colors and a permutation")
        return self.element_class(self, [self._C(v) for v in x[0]], self._P(x[1]))

    def _coerce_map_from_(self, C):
        """
        Return a coerce map from ``C`` if it exists and ``None`` otherwise.

        EXAMPLES::

            sage: C = ColoredPermutations(2, 3)
            sage: S = SignedPermutations(3)
            sage: C.has_coerce_map_from(S)
            True

            sage: C = ColoredPermutations(4, 3)
            sage: C.has_coerce_map_from(S)
            False
            sage: S = SignedPermutations(4)
            sage: C.has_coerce_map_from(S)
            False

            sage: P = Permutations(3)
            sage: C.has_coerce_map_from(P)
            True
            sage: P = Permutations(4)
            sage: C.has_coerce_map_from(P)
            False
        """
        if isinstance(C, Permutations) and C.n == self._n:
            return lambda P, x: P.element_class(P, [P._C.zero()] * P._n, x)
        if self._m == 2 and isinstance(C, SignedPermutations) and C._n == self._n:
            return lambda P, x: P.element_class(P,
                                                [P._C.zero() if v == 1 else P._C.one()
                                                 for v in x._colors],
                                                x._perm)
        return super()._coerce_map_from_(C)

    def __iter__(self):
        """
        Iterate over ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(2, 2)
            sage: [x for x in C]
            [[[0, 0], [1, 2]],
             [[0, 1], [1, 2]],
             [[1, 0], [1, 2]],
             [[1, 1], [1, 2]],
             [[0, 0], [2, 1]],
             [[0, 1], [2, 1]],
             [[1, 0], [2, 1]],
             [[1, 1], [2, 1]]]
        """
        for p in self._P:
            for c in itertools.product(self._C, repeat=self._n):
                yield self.element_class(self, c, p)

    def cardinality(self):
        """
        Return the cardinality of ``self``.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: C.cardinality()
            384
            sage: C.cardinality() == 4**3 * factorial(3)
            True
        """
        return self._m ** self._n * self._P.cardinality()

    order = cardinality

    def rank(self):
        """
        Return the rank of ``self``.

        The rank of a complex reflection group is equal to the dimension
        of the complex vector space the group acts on.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 12)
            sage: C.rank()
            12
            sage: C = ColoredPermutations(7, 4)
            sage: C.rank()
            4
            sage: C = ColoredPermutations(1, 4)
            sage: C.rank()
            3
        """
        if self._m == 1:
            return self._n - 1
        return self._n

    def degrees(self):
        r"""
        Return the degrees of ``self``.

        The degrees of a complex reflection group are the degrees of
        the fundamental invariants of the ring of polynomial invariants.

        If `m = 1`, then we are in the special case of the symmetric group
        and the degrees are `(2, 3, \ldots, n, n+1)`. Otherwise the degrees
        are `(m, 2m, \ldots, nm)`.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: C.degrees()
            (4, 8, 12)
            sage: S = ColoredPermutations(1, 3)
            sage: S.degrees()
            (2, 3)

        We now check that the product of the degrees is equal to the
        cardinality of ``self``::

            sage: prod(C.degrees()) == C.cardinality()
            True
            sage: prod(S.degrees()) == S.cardinality()
            True
        """
        # For the usual symmetric group (self._m=1) we need to start at 2
        start = 2 if self._m == 1 else 1
        return tuple(self._m * i for i in range(start, self._n + 1))

    def codegrees(self):
        r"""
        Return the codegrees of ``self``.

        Let `G` be a complex reflection group. The codegrees
        `d_1^* \leq d_2^* \leq \cdots \leq d_{\ell}^*` of `G` can be
        defined by:

        .. MATH::

            \prod_{i=1}^{\ell} (q - d_i^* - 1)
            = \sum_{g \in G} \det(g) q^{\dim(V^g)},

        where `V` is the natural complex vector space that `G` acts on
        and `\ell` is the :meth:`rank`.

        If `m = 1`, then we are in the special case of the symmetric group
        and the codegrees are `(n-2, n-3, \ldots 1, 0)`. Otherwise the degrees
        are `((n-1)m, (n-2)m, \ldots, m, 0)`.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: C.codegrees()
            (8, 4, 0)
            sage: S = ColoredPermutations(1, 3)
            sage: S.codegrees()
            (1, 0)

        TESTS:

        We check the polynomial identity::

            sage: R.<q> = ZZ[]
            sage: C = ColoredPermutations(3, 2)
            sage: f = prod(q - ds - 1 for ds in C.codegrees())
            sage: d = lambda x: sum(1 for e in x.to_matrix().eigenvalues() if e == 1)
            sage: g = sum(det(x.to_matrix()) * q**d(x) for x in C)                      # needs sage.modules sage.rings.number_field
            sage: f == g                                                                # needs sage.modules sage.rings.number_field
            True
        """
        # Special case for the usual symmetric group
        last = self._n - 1 if self._m == 1 else self._n
        return tuple(self._m * i for i in reversed(range(last)))

    def number_of_reflection_hyperplanes(self):
        """
        Return the number of reflection hyperplanes of ``self``.

        The number of reflection hyperplanes of a complex reflection
        group is equal to the sum of the codegrees plus the rank.

        EXAMPLES::

            sage: C = ColoredPermutations(1, 2)
            sage: C.number_of_reflection_hyperplanes()
            1
            sage: C = ColoredPermutations(1, 3)
            sage: C.number_of_reflection_hyperplanes()
            3
            sage: C = ColoredPermutations(4, 12)
            sage: C.number_of_reflection_hyperplanes()
            276
        """
        return sum(self.codegrees()) + self.rank()

    def fixed_point_polynomial(self, q=None):
        r"""
        The fixed point polynomial of ``self``.

        The fixed point polynomial `f_G` of a complex reflection group `G`
        is counting the dimensions of fixed points subspaces:

        .. MATH::

            f_G(q) = \sum_{w \in W} q^{\dim V^w}.

        Furthermore, let `d_1, d_2, \ldots, d_{\ell}` be the degrees of `G`,
        where `\ell` is the :meth:`rank`. Then the fixed point polynomial
        is given by

        .. MATH::

            f_G(q) = \prod_{i=1}^{\ell} (q + d_i - 1).

        INPUT:

        - ``q`` -- (default: the generator of ``ZZ['q']``) the parameter `q`

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: C.fixed_point_polynomial()
            q^3 + 21*q^2 + 131*q + 231

            sage: S = ColoredPermutations(1, 3)
            sage: S.fixed_point_polynomial()
            q^2 + 3*q + 2

        TESTS:

        We check the against the degrees and codegrees::

            sage: R.<q> = ZZ[]
            sage: C = ColoredPermutations(4, 3)
            sage: C.fixed_point_polynomial(q) == prod(q + d - 1 for d in C.degrees())
            True
        """
        if q is None:
            q = PolynomialRing(ZZ, 'q').gen(0)
        return prod(q + d - 1 for d in self.degrees())

    def is_well_generated(self):
        r"""
        Return if ``self`` is a well-generated complex reflection group.

        A complex reflection group `G` is well-generated if it is
        generated by `\ell` reflections. Equivalently, `G` is well-generated
        if `d_i + d_i^* = d_{\ell}` for all `1 \leq i \leq \ell`.

        EXAMPLES::

            sage: C = ColoredPermutations(4, 3)
            sage: C.is_well_generated()
            True
            sage: C = ColoredPermutations(2, 8)
            sage: C.is_well_generated()
            True
            sage: C = ColoredPermutations(1, 4)
            sage: C.is_well_generated()
            True
        """
        deg = self.degrees()
        codeg = self.codegrees()
        return all(deg[-1] == d + dstar for d, dstar in zip(deg, codeg))

    Element = ColoredPermutation


#####################################################################
#  Signed permutations


class SignedPermutation(ColoredPermutation,
                        metaclass=InheritComparisonClasscallMetaclass):
    """
    A signed permutation.
    """
    @staticmethod
    def __classcall_private__(cls, pi):
        """
        Create a signed permutation.

        EXAMPLES::

            sage: SignedPermutation([2, 1, 3])
            [2, 1, 3]

            sage: SignedPermutation([2, 1, -3])
            [2, 1, -3]

            sage: SignedPermutation((2,1,-3))
            [2, 1, -3]

            sage: SignedPermutation(range(1,4))
            [1, 2, 3]
        """
        return SignedPermutations(len(list(pi)))(pi)

    def _repr_(self):
        """
        Return a string representation of ``self``.

        EXAMPLES::

            sage: S = SignedPermutations(4)
            sage: s1,s2,s3,s4 = S.gens()
            sage: s4*s1*s2*s3*s4
            [-4, 1, 2, -3]
        """
        return repr(list(self))

    _latex_ = _repr_

    def _mul_(self, other):
        """
        Multiply ``self`` and ``other``.

        EXAMPLES::

            sage: S = SignedPermutations(4)
            sage: s1,s2,s3,s4 = S.gens()
            sage: x = s4*s1*s2*s3*s4; x
            [-4, 1, 2, -3]
            sage: x * x
            [3, -4, 1, -2]

        ::

            sage: s1*s2*s1 == s1*s2*s1
            True
            sage: s3*s4*s3*s4 == s4*s3*s4*s3
            True
        """
        colors = tuple(c * other._colors[val - 1]  # -1 for indexing
                       for c, val in zip(self._colors, self._perm))
        p = self._perm._left_to_right_multiply_on_right(other._perm)
        return self.__class__(self.parent(), colors, p)

    def __invert__(self):
        """
        Return the inverse of ``self``.

        EXAMPLES::

            sage: S = SignedPermutations(4)
            sage: s1,s2,s3,s4 = S.gens()
            sage: x = s4*s1*s2*s3*s4
            sage: ~x   # indirect doctest
            [2, 3, -4, -1]
            sage: x * ~x == S.one()
            True
        """
        ip = ~self._perm
        return self.__class__(self.parent(),
                              tuple(self._colors[i - 1] for i in ip),  # -1 for indexing
                              ip)

    def __iter__(self):
        """
        Iterate over ``self``.

        EXAMPLES::

            sage: S = SignedPermutations(4)
            sage: s1,s2,s3,s4 = S.gens()
            sage: x = s4*s1*s2*s3*s4
            sage: [a for a in x]
            [-4, 1, 2, -3]
        """
        for c, p in zip(self._colors, self._perm):
            yield c * p

    def __getitem__(self, key):
        """
        Return the specified element in the one line form of ``self``.

        EXAMPLES::

            sage: pi = SignedPermutation([-4, 5, -1, 2, -3])
            sage: pi[-1]
            -3
            sage: pi[1::2]
            [5, 2]
        """
        if isinstance(key, slice):
            return [c * v for c, v in zip(self._colors[key], self._perm[key])]
        return self._colors[key] * self._perm[key]

    def __call__(self, i):
        """
        Return the image of the integer ``i`` in ``self``.

        EXAMPLES::

            sage: pi = SignedPermutations(7)([2,-1,4,-6,-5,-3,7])
            sage: pi(2)
            -1
            sage: pi(-2)
            1
            sage: pi(7)
            7
            sage: pi(-7)
            -7
            sage: [pi(i) for i in range(1,8)]
            [2, -1, 4, -6, -5, -3, 7]
            sage: [pi(-i) for i in range(1,8)]
            [-2, 1, -4, 6, 5, 3, -7]
        """
        if i in ZZ and 1 <= abs(i) <= len(self):
            i = ZZ(i)
            if i < 0:
                return -self._colors[-i - 1] * self._perm[-i - 1]
            return self._colors[i - 1] * self._perm[i - 1]

        raise TypeError("i (= %s) must equal +/- an integer between %s and %s"
                        % (i, 1, len(self)))

    def to_matrix(self):
        """
        Return a matrix of ``self``.

        EXAMPLES::

            sage: S = SignedPermutations(4)
            sage: s1,s2,s3,s4 = S.gens()
            sage: x = s4*s1*s2*s3*s4
            sage: M = x.to_matrix(); M                                                  # needs sage.modules
            [ 0  1  0  0]
            [ 0  0  1  0]
            [ 0  0  0 -1]
            [-1  0  0  0]

        The matrix multiplication is in the *opposite* order::

            sage: m1,m2,m3,m4 = [g.to_matrix() for g in S.gens()]                       # needs sage.modules
            sage: M == m4 * m3 * m2 * m1 * m4                                           # needs sage.modules
            True
        """
        return self._perm.to_matrix() * diagonal_matrix(self._colors)

    def has_left_descent(self, i):
        """
        Return ``True`` if ``i`` is a left descent of ``self``.

        EXAMPLES::

            sage: S = SignedPermutations(4)
            sage: s1,s2,s3,s4 = S.gens()
            sage: x = s4*s1*s2*s3*s4
            sage: [x.has_left_descent(i) for i in S.index_set()]
            [True, False, False, True]
        """
        n = self.parent()._n
        if i == n:
            return self._colors[-1] == -1
        if self._colors[i - 1] == -1:
            return self._colors[i] == 1 or self._perm[i - 1] < self._perm[i]
        return self._colors[i] == 1 and self._perm[i - 1] > self._perm[i]

    def to_cycles(self, singletons=True, use_min=True, negative_cycles=True):
        r"""
        Return the signed permutation ``self`` as a list of disjoint cycles.

        The cycles are returned in the order of increasing smallest
        elements, and each cycle is returned as a tuple which starts
        with its smallest positive element.

        INPUT:

        - ``singletons`` -- (default: ``True``) whether to include singleton
          cycles or not
        - ``use_min`` -- (default: ``True``) if ``False``, the cycles are
          returned in the order of increasing *largest* (not smallest)
          elements, and each cycle starts with its largest element
        - ``negative_cycles`` -- (default: ``True``) if ``False``, for any
          two cycles `C^{\pm} = \{\pm c_1, \ldots, \pm c_k\}` such that
          `C^+ \neq C^-`, this does not include the cycle `C^-`

        .. WARNING::

            The arugment ``negative_cycles`` does not refer to the usual
            definition of a negative cycle; see :meth:`cycle_type`.

        EXAMPLES::

            sage: pi = SignedPermutations(7)([2,-1,4,-6,-5,-3,7])
            sage: pi.to_cycles()
            [(1, 2, -1, -2), (3, 4, -6), (-3, -4, 6), (5, -5), (7,), (-7,)]
            sage: pi.to_cycles(singletons=False)
            [(1, 2, -1, -2), (3, 4, -6), (-3, -4, 6), (5, -5)]
            sage: pi.to_cycles(negative_cycles=False)
            [(1, 2, -1, -2), (3, 4, -6), (5, -5), (7,)]
            sage: pi.to_cycles(singletons=False, negative_cycles=False)
            [(1, 2, -1, -2), (3, 4, -6), (5, -5)]
            sage: pi.to_cycles(use_min=False)
            [(7,), (-7,), (6, -3, -4), (-6, 3, 4), (5, -5), (2, -1, -2, 1)]
            sage: pi.to_cycles(singletons=False, use_min=False)
            [(6, -3, -4), (-6, 3, 4), (5, -5), (2, -1, -2, 1)]
        """
        cycles = []

        l = self._perm[:]

        if use_min:
            groundset = range(len(l))
        else:
            groundset = reversed(range(len(l)))

        # Go through until we've considered every number between 1 and len(l)
        for i in groundset:
            if not l[i]:
                continue
            cycle_first = i + 1
            cycle = [cycle_first]
            l[i], next_val = False, l[i]
            s = self._colors[i]
            add_neg = True
            while next_val != cycle_first:
                cycle.append(s * next_val)
                s *= self._colors[next_val - 1]
                l[next_val - 1], next_val = False, l[next_val - 1]
            if s != 1:
                cycle.extend([-e for e in cycle])
                add_neg = False

            # Add the cycle to the list of cycles
            if singletons or len(cycle) > 1:
                cycles.append(tuple(cycle))
                if negative_cycles and add_neg:
                    cycles.append(tuple([-e for e in cycle]))

        return cycles

    def cycle_type(self):
        r"""
        Return a pair of partitions of ``len(self)`` corresponding to the
        signed cycle type of ``self``.

        A *cycle* is a tuple `C = (c_0, \ldots, c_{k-1})` with
        `\pi(c_i) = c_{i+1}` for `0 \leq i < k` and `\pi(c_{k-1}) = c_0`.
        If `C` is a cycle, `\overline{C} = (-c_0, \ldots, -c_{k-1})` is
        also a cycle. A cycle is *negative*, if `C = \overline{C}` up
        to cyclic reordering. In this case, `k` is necessarily even
        and the length of `C` is `k/2`. A *positive cycle* is a pair
        `C \overline{C}`, its length is `k`.

        Let `\alpha` be the partition whose parts are the lengths of the
        positive cycles and let `\beta` be the partition whose parts are
        the lengths of the negative cycles.  Then `(\alpha, \beta)` is
        the cycle type of `\pi`.

        EXAMPLES::

            sage: G = SignedPermutations(7)
            sage: pi = G([2, -1, 4, -6, -5, -3, 7])
            sage: pi.cycle_type()
            ([3, 1], [2, 1])

            sage: G = SignedPermutations(5)
            sage: all(pi.cycle_type().size() == 5 for pi in G)
            True
            sage: set(pi.cycle_type() for pi in G) == set(PartitionTuples(2, 5))
            True
        """
        cycles = self.to_cycles(negative_cycles=False)
        pos_cycles = []
        neg_cycles = []
        for C in cycles:
            if (not len(C) % 2) and C[0] == -C[len(C)//2]:
                neg_cycles.append(C)
            else:
                pos_cycles.append(C)
        pos_type = [len(C) for C in pos_cycles]
        pos_type.sort(reverse=True)
        neg_type = [len(C) // 2 for C in neg_cycles]
        neg_type.sort(reverse=True)
        from sage.combinat.partition_tuple import PartitionTuples
        PT = PartitionTuples(2, self.parent()._n)
        return PT([pos_type, neg_type])

    def order(self):
        """
        Return the multiplicative order of the signed permutation.

        EXAMPLES::

            sage: pi = SignedPermutations(7)([2,-1,4,-6,-5,-3,7])
            sage: pi.to_cycles(singletons=False)
            [(1, 2, -1, -2), (3, 4, -6), (-3, -4, 6), (5, -5)]
            sage: pi.order()
            12
        """
        return lcm(len(c) for c in self.to_cycles(singletons=False, negative_cycles=False))


class SignedPermutations(ColoredPermutations):
    r"""
    Group of signed permutations.

    The group of signed permutations is also known as the hyperoctahedral
    group, the Coxeter group of type `B_n`, and the 2-colored permutation
    group. Thus it can be constructed as the wreath product `S_2 \wr S_n`.

    EXAMPLES::

        sage: S = SignedPermutations(4)
        sage: s1,s2,s3,s4 = S.group_generators()
        sage: x = s4*s1*s2*s3*s4; x
        [-4, 1, 2, -3]
        sage: x^4 == S.one()
        True

    This is a finite Coxeter group of type `B_n`::

        sage: S.canonical_representation()                                              # needs sage.modules
        Finite Coxeter group over Number Field in a with defining polynomial x^2 - 2
         with a = 1.414213562373095? with Coxeter matrix:
        [1 3 2 2]
        [3 1 3 2]
        [2 3 1 4]
        [2 2 4 1]
        sage: S.long_element()
        [-1, -2, -3, -4]
        sage: S.long_element().reduced_word()
        [1, 2, 1, 3, 2, 1, 4, 3, 2, 1, 4, 3, 2, 4, 3, 4]

    We can also go between the 2-colored permutation group::

        sage: C = ColoredPermutations(2, 3)
        sage: S = SignedPermutations(3)
        sage: S.an_element()
        [-3, 1, 2]
        sage: C(S.an_element())
        [[1, 0, 0], [3, 1, 2]]
        sage: S(C(S.an_element())) == S.an_element()
        True
        sage: S(C.an_element())
        [-3, 1, 2]

    There is also the natural lift from permutations::

        sage: P = Permutations(3)
        sage: x = S(P.an_element()); x
        [3, 1, 2]
        sage: x.parent()
        Signed permutations of 3

    REFERENCES:

    - :wikipedia:`Hyperoctahedral_group`
    """
    def __init__(self, n):
        """
        Initialize ``self``.

        EXAMPLES::

            sage: S = SignedPermutations(4)
            sage: TestSuite(S).run()
        """
        ColoredPermutations.__init__(self, 2, n)

    def _repr_(self):
        """
        Return a string representation of ``self``.

        EXAMPLES::

            sage: SignedPermutations(4)
            Signed permutations of 4
        """
        return "Signed permutations of {}".format(self._n)

    @cached_method
    def one(self):
        """
        Return the identity element of ``self``.

        EXAMPLES::

            sage: S = SignedPermutations(4)
            sage: S.one()
            [1, 2, 3, 4]
        """
        return self.element_class(self, [ZZ.one()] * self._n,
                                  self._P.identity())

    def random_element(self):
        """
        Return an element drawn uniformly at random.

        EXAMPLES::

            sage: C = SignedPermutations(7)
            sage: s = C.random_element(); s # random
            [7, 6, -4, -5, 2, 3, -1]
            sage: s in C
            True
        """
        return self.element_class(self,
                                  [choice([ZZ.one(), -ZZ.one()])
                                   for _ in range(self._n)],
                                  self._P.random_element())

    def simple_reflection(self, i):
        r"""
        Return the ``i``-th simple reflection of ``self``.

        EXAMPLES::

            sage: S = SignedPermutations(4)
            sage: S.simple_reflection(1)
            [2, 1, 3, 4]
            sage: S.simple_reflection(4)
            [1, 2, 3, -4]
        """
        if i not in self.index_set():
            raise ValueError("i must be in the index set")
        if i < self._n:
            p = list(range(1, self._n + 1))
            p[i - 1] = i + 1
            p[i] = i
            return self.element_class(self, [ZZ.one()] * self._n, self._P(p))
        temp = [ZZ.one()] * self._n
        temp[-1] = -ZZ.one()
        return self.element_class(self, temp, self._P.identity())

    def _element_constructor_(self, x):
        """
        Construct an element of ``self`` from ``x``.

        TESTS::

            sage: S = SignedPermutations(3)
            sage: x = S([(+1,1), (-1,3), (-1,2)]); x
            [1, -3, -2]
            sage: x == S([[+1,-1,-1], [1,3,2]])
            True
            sage: x == S([1, -3, -2])
            True

            sage: S = SignedPermutations(0)
            sage: S([]) == list(S)[0]
            True

            sage: T = SignedPermutation(range(1,4))
            sage: SignedPermutations(3)(T)
            [1, 2, 3]
        """
        if isinstance(x, self.element_class) and x.parent() is self:
            return self
        x = list(x)
        if x and isinstance(x[0], tuple):
            c = []
            p = []
            for k in x:
                if len(k) != 2:
                    raise ValueError("input must be pairs (sign, element)")
                if k[0] != 1 and k[0] != -1:
                    raise ValueError("the sign must be +1 or -1")
                c.append(ZZ(k[0]))
                p.append(k[1])
            return self.element_class(self, c, self._P(p))

        if len(x) == self._n:
            c = []
            p = []
            one = ZZ.one()
            for v in x:
                if v > 0:
                    c.append(one)
                    p.append(v)
                else:
                    c.append(-one)
                    p.append(-v)
            return self.element_class(self, c, self._P(p))

        if len(x) != 2:
            raise ValueError("input must be a pair of a list of signs and a permutation")
        if any(s != 1 and s != -1 for s in x[0]):
            raise ValueError("the sign must be +1 or -1")
        return self.element_class(self, [ZZ(v) for v in x[0]], self._P(x[1]))

    def __iter__(self):
        """
        Iterate over ``self``.

        EXAMPLES::

            sage: S = SignedPermutations(2)
            sage: [x for x in S]
            [[1, 2], [1, -2], [-1, 2], [-1, -2],
             [2, 1], [2, -1], [-2, 1], [-2, -1]]
        """
        pmone = [ZZ.one(), -ZZ.one()]
        for p in self._P:
            for c in itertools.product(pmone, repeat=self._n):
                yield self.element_class(self, c, p)

    def _coerce_map_from_(self, C):
        """
        Return a coerce map from ``C`` if it exists and ``None`` otherwise.

        EXAMPLES::

            sage: C = ColoredPermutations(2, 3)
            sage: S = SignedPermutations(3)
            sage: S.has_coerce_map_from(C)
            True

            sage: C = ColoredPermutations(4, 3)
            sage: S.has_coerce_map_from(C)
            False

            sage: P = Permutations(3)
            sage: C.has_coerce_map_from(P)
            True
            sage: P = Permutations(4)
            sage: C.has_coerce_map_from(P)
            False
        """
        if isinstance(C, Permutations) and C.n == self._n:
            return lambda P, x: P.element_class(P, [1] * P._n, x)
        if isinstance(C, ColoredPermutations) and C._n == self._n and C._m == 2:
            return lambda P, x: P.element_class(P,
                                                [1 if v == 0 else -1
                                                 for v in x._colors],
                                                x._perm)
        return super()._coerce_map_from_(C)

    def tabloid_module(self, shape, base_ring):
        return TabloidModule(self, base_ring, shape)

    def specht_module(self, shape, base_ring):
        return self.tabloid_module(shape, base_ring).specht_module()

    def simple_module(self, shape, base_ring):
        return self.specht_module(shape, base_ring).simple_module()

    def long_element(self, index_set=None):
        """
        Return the longest element of ``self``, or of the
        parabolic subgroup corresponding to the given ``index_set``.

        INPUT:

        - ``index_set`` -- (optional) a subset (as a list or iterable)
          of the nodes of the indexing set

        EXAMPLES::

            sage: S = SignedPermutations(4)
            sage: S.long_element()
            [-1, -2, -3, -4]

        TESTS:

        Check that this is the element of maximal length (:issue:`25200`)::

            sage: S = SignedPermutations(4)
            sage: S.long_element().length() == max(x.length() for x in S)
            True
            sage: all(SignedPermutations(n).long_element().length() == n^2
            ....:     for n in range(2,10))
            True
        """
        if index_set is not None:
            return super().long_element()
        return self.element_class(self, [-ZZ.one()] * self._n, self._P.one())

    def conjugacy_class_representative(self, nu):
        r"""
        Return a permutation with (signed) cycle type ``nu``.

        EXAMPLES::

            sage: G = SignedPermutations(4)
            sage: for nu in PartitionTuples(2, 4):
            ....:     print(nu, G.conjugacy_class_representative(nu))
            ....:     assert nu == G.conjugacy_class_representative(nu).cycle_type(), nu
            ([4], []) [2, 3, 4, 1]
            ([3, 1], []) [2, 3, 1, 4]
            ([2, 2], []) [2, 1, 4, 3]
            ([2, 1, 1], []) [2, 1, 3, 4]
            ([1, 1, 1, 1], []) [1, 2, 3, 4]
            ([3], [1]) [2, 3, 1, -4]
            ([2, 1], [1]) [2, 1, 3, -4]
            ([1, 1, 1], [1]) [1, 2, 3, -4]
            ([2], [2]) [2, 1, 4, -3]
            ([2], [1, 1]) [2, 1, -3, -4]
            ([1, 1], [2]) [1, 2, 4, -3]
            ([1, 1], [1, 1]) [1, 2, -3, -4]
            ([1], [3]) [1, 3, 4, -2]
            ([1], [2, 1]) [1, 3, -2, -4]
            ([1], [1, 1, 1]) [1, -2, -3, -4]
            ([], [4]) [2, 3, 4, -1]
            ([], [3, 1]) [2, 3, -1, -4]
            ([], [2, 2]) [2, -1, 4, -3]
            ([], [2, 1, 1]) [2, -1, -3, -4]
            ([], [1, 1, 1, 1]) [-1, -2, -3, -4]

        TESTS::

            sage: all(nu == SignedPermutations(n).conjugacy_class_representative(nu).cycle_type()
            ....:     for n in range(1, 6) for nu in PartitionTuples(2, n))
            True
        """
        from sage.combinat.partition_tuple import PartitionTuple
        nu = PartitionTuple(nu)
        if nu.size() != self._n:
            raise ValueError("the size of the partition pair (=%s) must equal"
                             " the rank (=%s)" % (nu.size(), self._n))
        la, mu = nu
        cyc = []
        cnt = 0

        for i in la:
            cyc += [tuple(range(cnt+1, cnt+i+1))] + [tuple(range(-cnt-1, -cnt-i-1, -1))]
            cnt += i
        for i in mu:
            cyc += [tuple(range(cnt+1, cnt+i+1)) + tuple(range(-cnt-1, -cnt-i-1, -1))]
            cnt += i

        p = [None] * self._n
        for c in cyc:
            for i in range(len(c)-1):
                if c[i] > 0:
                    p[c[i]-1] = c[i+1]
            if c[-1] > 0:
                p[c[-1]-1] = c[0]

        return self(p)

    Element = SignedPermutation

# TODO: Make this a subgroup
# class EvenSignedPermutations(SignedPermutations):
#    """
#    Group of even signed permutations.
#    """
#    def _repr_(self):
#        """
#        Return a string representation of ``self``.
#        """
#        return "Even signed permutations of {}".format(self._n)
#
#    def __iter__(self):
#        """
#        Iterate over ``self``.
#        """
#        for s in SignedPermutations.__iter__(self):
#            total = 0
#            for pm in s._colors:
#                if pm == -1:
#                    total += 1
#
#            if total % 2 == 0:
#                yield s

# ===================================================================
# Representation theory


class TabloidModule(Representation_abstract, CombinatorialFreeModule):
    r"""
    The vector space of all tabloids of a fixed shape with the natural
    signed permutation group action.

    A *tabloid* of size `n` is a pair of squences sets `(S, T)` such that:

    - For all `X, Y \in S \cup T`, we have `X \cap Y = \emptyset`
      (all sets are pairwise disjoint).
    - `\sum_{X \in S \cup T} |X| = n`.
    - `\bigsqcup_{X\subseteq S \cup T} X \sqcup \overline{X} = \{1, \ldots,
      n, \overline{1} \ldots, \overline{n}\}`.

    The signed permutation group acts naturally on the entries of each set.
    Hence, this is a representation of the signed permutation group
    defined over any field.

    EXAMPLES::

        sage: SP5 = SignedPermutations(5)
        sage: TM = SP5.tabloid_module(GF(3), [[2, 1], [2]])
        sage: TM.dimension()
        30
        sage: TM.brauer_character()
        (30, 6, 2, 0, 0)
        sage: IM = TM.invariant_module()
        sage: IM.dimension()
        1
        sage: IM.basis()[0].lift() == sum(TM.basis())
        True

    We verify the dimension is `2^{|\lambda|} \frac{n!}{
    \lambda_1! \cdots \lambda_{\ell}! \mu_1! \cdots \mu_m!}`::

    REFERENCES:

    - [Morris1981]_
    """
    @staticmethod
    def __classcall_private__(cls, G, base_ring, shape):
        r"""
        Normalize input to ensure a unique representation.

        EXAMPLES::

            sage: from sage.combinat.specht_module import TabloidModule
            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: TM1 = TabloidModule(SGA, [2, 2, 1])
            sage: TM2 = TabloidModule(SGA, Partition([2, 2, 1]))
            sage: TM1 is TM2
            True

            sage: TabloidModule(SGA, [3, 2, 1])
            Traceback (most recent call last):
            ...
            ValueError: the domain size (=5) does not match the number of boxes (=6) of the diagram
        """
        from sage.combinat.partition_tuple import PartitionTuples
        shape = PartitionTuples(2, G._n)(shape)
        return super().__classcall__(cls, G, base_ring, shape)

    def __init__(self, G, base_ring, shape):
        r"""
        Initialize ``self``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: TM = SGA.tabloid_module([2,2,1])
            sage: TestSuite(TM).run()
        """
        self._shape = shape
        from sage.categories.modules_with_basis import ModulesWithBasis
        cat = ModulesWithBasis(base_ring).FiniteDimensional()

        # Build the tabloids
        from sage.sets.disjoint_union_enumerated_sets import DisjointUnionEnumeratedSets
        from sage.combinat.set_partition_ordered import OrderedSetPartitions
        from sage.categories.sets_cat import cartesian_product
        from itertools import product
        la, mu = self._shape
        data = [cartesian_product([OrderedSetPartitions([val * x for x, val in zip(sorted(X), signs)], la),
                                   OrderedSetPartitions(sorted(Y), mu)])
                for (X, Y) in OrderedSetPartitions(G._n, [sum(la), sum(mu)])
                for signs in product([1,-1], repeat=sum(la))]
        tabloids = DisjointUnionEnumeratedSets(data)
        tabloids.rename(f"Tabloids of shape {self._shape}")

        Representation_abstract.__init__(self, G, base_ring, "left", tabloids,
                                         category=cat, prefix='T', bracket='')

    def _repr_(self):
        r"""
        Return a string representation of ``self``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: SGA.tabloid_module([2,2,1])
            Tabloid module of [2, 2, 1] over Rational Field
        """
        return f"Tabloid module of {self._shape} over {self.base_ring()}"

    def _latex_(self):
        r"""
        Return a latex representation of ``self``.

        EXAMPLES::

            sage: B4 = SignedPermutations(4)
            sage: TM = B4.tabloid_module([[2,1],[1]], GF(3))
            sage: latex(TM)
            T^{{\def\lr#1{\multicolumn{1}{|@{\hspace{.6ex}}c@{\hspace{.6ex}}|}{\raisebox{-.3ex}{$#1$}}}
            \raisebox{-.6ex}{$\begin{array}[b]{*{2}c}\cline{1-2}
            \lr{\phantom{x}}&\lr{\phantom{x}}\\\cline{1-2}
            \lr{\phantom{x}}\\\cline{1-1}
            \end{array}$}
            },{\def\lr#1{\multicolumn{1}{|@{\hspace{.6ex}}c@{\hspace{.6ex}}|}{\raisebox{-.3ex}{$#1$}}}
            \raisebox{-.6ex}{$\begin{array}[b]{*{1}c}\cline{1-1}
            \lr{\phantom{x}}\\\cline{1-1}
            \end{array}$}
            }}
        """
        from sage.misc.latex import latex
        return "T^{" + ",".join(latex(la) for la in self._shape) + "}"

    def _ascii_art_term(self, TP):
        r"""
        Return an ascii art representation of the term indexed by ``T``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: TM = SGA.tabloid_module([2,2,1])
            sage: ascii_art(TM.an_element())  # indirect doctest
            2*T       + 2*T       + 3*T
               {1, 2}      {1, 2}      {1, 2}
               {3, 4}      {3, 5}      {4, 5}
               {5}         {4}         {3}
        """
        # This is basically copied from CombinatorialFreeModule._ascii_art_term
        from sage.typeset.ascii_art import AsciiArt, ascii_art
        pref = AsciiArt([self.prefix()])
        data = []
        for T in TP:
            tab = "\n".join("{" + ", ".join(str(val) for val in sorted(row)) + "}" for row in T)
            if not tab:
                tab = '-'
            data.append(tab)
        r = pref * (AsciiArt([" " * len(pref)]) + ascii_art(data[0]) + ascii_art(', ') + ascii_art(data[1]))
        r._baseline = r._h - 1
        return r

    def _unicode_art_term(self, T):
        r"""
        Return a unicode art representation of the term indexed by ``T``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: TM = SGA.tabloid_module([2,2,1])
            sage: unicode_art(TM.an_element())  # indirect doctest
            2*T       + 2*T       + 3*T
               {1, 2}      {1, 2}      {1, 2}
               {3, 4}      {3, 5}      {4, 5}
               {5}         {4}         {3}
        """
        from sage.typeset.unicode_art import unicode_art
        r = unicode_art(repr(self._ascii_art_term(T)))
        r._baseline = r._h - 1
        return r

    def _latex_term(self, TP):
        r"""
        Return a latex representation of the term indexed by ``T``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: TM = SGA.tabloid_module([2,2,1])
            sage: latex(TM.an_element())  # indirect doctest
            2 T_{{\def\lr#1{\multicolumn{1}{@{\hspace{.6ex}}c@{\hspace{.6ex}}}{\raisebox{-.3ex}{$#1$}}}
            \raisebox{-.6ex}{$\begin{array}[b]{*{2}c}\cline{1-2}
            \lr{1}&\lr{2}\\\cline{1-2}
            \lr{3}&\lr{4}\\\cline{1-2}
            \lr{5}\\\cline{1-1}
            \end{array}$}
            }} + 2 T_{{\def\lr#1{\multicolumn{1}{@{\hspace{.6ex}}c@{\hspace{.6ex}}}{\raisebox{-.3ex}{$#1$}}}
            \raisebox{-.6ex}{$\begin{array}[b]{*{2}c}\cline{1-2}
            \lr{1}&\lr{2}\\\cline{1-2}
            \lr{3}&\lr{5}\\\cline{1-2}
            \lr{4}\\\cline{1-1}
            \end{array}$}
            }} + 3 T_{{\def\lr#1{\multicolumn{1}{@{\hspace{.6ex}}c@{\hspace{.6ex}}}{\raisebox{-.3ex}{$#1$}}}
            \raisebox{-.6ex}{$\begin{array}[b]{*{2}c}\cline{1-2}
            \lr{1}&\lr{2}\\\cline{1-2}
            \lr{4}&\lr{5}\\\cline{1-2}
            \lr{3}\\\cline{1-1}
            \end{array}$}
            }}
        """
        data = []
        import re
        for T in TP:
            if not T:
                tab = "\\emptyset"
            else:
                from sage.combinat.output import tex_from_array
                A = list(map(sorted, T))
                tab = str(tex_from_array(A))
                tab = tab.replace("|", "")
                # Replace -i with \overline{i} in boxes
                tab = re.sub(r"\\lr{-([0-9]+)}", r"\\lr{\\overline{\1}}", tab)
            data.append(tab)
        return f"{self.prefix()}_{{{data[0]}, {data[1]}}}"

    def _semigroup_basis_action(self, g, T):
        P = self._indices
        #g = self._semigroup(g)
        U = [[g(val) for val in row] for row in T[0]]
        V = [[abs(g(val)) for val in row] for row in T[1]]
        return P([U, V])

    def _semigroup_action(self, g, vec, vec_on_left):
        r"""
        Return the action of the symmetric group element ``g`` on the
        ordered set partition ``osp``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: TM = SGA.tabloid_module([2,2,1])
            sage: osp = TM._indices([[1,4],[3,5],[2]])
            sage: g = SGA.group().an_element(); g
            [5, 1, 2, 3, 4]
            sage: TM._symmetric_group_action(osp, g)
            [{3, 5}, {2, 4}, {1}]
        """
        if self._left_repr == vec_on_left:
            g = ~g
        return self.sum_of_terms((self._semigroup_basis_action(g, T), c)
                                 for T, c in vec._monomial_coefficients.items())

    def specht_module(self):
        r"""
        Return the Specht submodule of ``self``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: TM = SGA.tabloid_module([2,2,1])
            sage: TM.specht_module() is SGA.specht_module([2,2,1])
            True
        """
        return SpechtModule(self)

    def bilinear_form(self, u, v):
        r"""
        Return the natural bilinear form of ``self`` applied to ``u`` and ``v``.

        The natural bilinear form is given by defining the tabloid basis
        to be orthonormal.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: TM = SGA.tabloid_module([2,2,1])
            sage: u = TM.an_element(); u
            2*T[{1, 2}, {3, 4}, {5}] + 2*T[{1, 2}, {3, 5}, {4}] + 3*T[{1, 2}, {4, 5}, {3}]
            sage: v = sum(TM.basis())
            sage: TM.bilinear_form(u, v)
            7
            sage: TM.bilinear_form(u, TM.zero())
            0
        """
        if len(v) < len(u):
            u, v = v, u
        R = self.base_ring()
        return R.sum(c * v[T] for T, c in u)


class SpechtModule(Representation_abstract, SubmoduleWithBasis):
    r"""
    A Specht module of a type `B_n` Coxeter group in the classical standard
    tableau pair basis.

    This is constructed as a `B_n`-submodule of the :class:`TabloidModule`
    (also referred to as the standard module) using the polytabloid elements
    associated to the standard tableaux of shape `(\lambda, \mu)`.

    We verify the set of 2-regular partitions for `n = 4`::

        sage: for la in PartitionTuples(2, 4):
        ....:     SM = B4.specht_module(la, GF(3))
        ....:     if SM.gram_matrix():
        ....:         print(la)
        ([4], [])
        ([3, 1], [])
        ([2, 2], [])
        ([2, 1, 1], [])
        ([3], [1])
        ([2, 1], [1])
        ([2], [2])
        ([2], [1, 1])
        ([1, 1], [2])
        ([1, 1], [1, 1])
        ([1], [3])
        ([1], [2, 1])
        ([], [4])
        ([], [3, 1])
        ([], [2, 2])
        ([], [2, 1, 1])
        sage: for la in PartitionTuples(2, 4):
        ....:     SM = B4.specht_module(la, GF(2))
        ....:     if SM.gram_matrix():
        ....:         print(la)
        ([], [4])
        ([], [3, 1])

    REFERENCES:

    - [Morris1981]_
    """
    def __init__(self, ambient):
        r"""
        Initialize ``self``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: SM = SGA.specht_module([2,2,1])
            sage: TestSuite(SM).run()
        """
        self._diagram = ambient._shape
        self._semigroup = ambient._semigroup
        self._semigroup_algebra = ambient._semigroup_algebra
        self._side = ambient._side
        self._left_repr = ambient._left_repr
        self._right_repr = ambient._right_repr

        ambient_basis = ambient.basis()
        tabloids = ambient_basis.keys()
        support_order = list(tabloids)
        from itertools import product

        def elt(T):
            tab = tabloids(list(T))

            def group_elements(sigma):
                mu_vals = set(sum((row for row in T[1]), ()))
                n = T.size()
                for sigma in T.column_stabilizer():
                    sigma = sigma.tuple()
                    for signs in product(*[[1,-1] if i not in mu_vals else [1]
                                           for i in range(1,n+1)]):
                        yield self._semigroup([s * val for s, val in zip(signs, sigma)])

            return ambient.sum_of_terms((ambient._semigroup_basis_action(elt, tab),
                                         1 - 2*(elt.length() % 2))  # == (-1)**elt.length()
                                        for elt in group_elements(T))

        from sage.sets.family import Family
        basis = Family({T: elt(T)
                        for T in self._diagram.standard_tableaux()})
        cat = ambient.category().Subobjects()
        SubmoduleWithBasis.__init__(self, basis, support_order, ambient=ambient,
                                    unitriangular=False, category=cat,
                                    prefix='S', bracket='')

    def _repr_(self):
        return "Specht module of shape {} over {}".format(self._diagram, self.base_ring())

    def _latex_(self):
        r"""
        Return a latex representation of ``self``.

        EXAMPLES::

            sage: B4 = SignedPermutations(4)
            sage: latex(B4.specht_module([[2,1],[1]], GF(3)))
            S^{{\def\lr#1{\multicolumn{1}{|@{\hspace{.6ex}}c@{\hspace{.6ex}}|}{\raisebox{-.3ex}{$#1$}}}
            \raisebox{-.6ex}{$\begin{array}[b]{*{2}c}\cline{1-2}
            \lr{\phantom{x}}&\lr{\phantom{x}}\\\cline{1-2}
            \lr{\phantom{x}}\\\cline{1-1}
            \end{array}$}
            },{\def\lr#1{\multicolumn{1}{|@{\hspace{.6ex}}c@{\hspace{.6ex}}|}{\raisebox{-.3ex}{$#1$}}}
            \raisebox{-.6ex}{$\begin{array}[b]{*{1}c}\cline{1-1}
            \lr{\phantom{x}}\\\cline{1-1}
            \end{array}$}
            }}
        """
        from sage.misc.latex import latex
        return "S^{" + ",".join(latex(la) for la in self._shape) + "}"

    @lazy_attribute
    def lift(self):
        r"""
        The lift (embedding) map from ``self`` to the ambient space.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: SM = SGA.specht_module([3, 1, 1])
            sage: SM.lift
            Generic morphism:
              From: Specht module of [3, 1, 1] over Rational Field
              To:   Tabloid module of [3, 1, 1] over Rational Field
        """
        return self.module_morphism(self.lift_on_basis, codomain=self.ambient())

    @lazy_attribute
    def retract(self):
        r"""
        The retract map from the ambient space.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: X = SGA.tabloid_module([2,2,1])
            sage: Y = X.specht_module()
            sage: Y.retract
            Generic morphism:
              From: Tabloid module of [2, 2, 1] over Rational Field
              To:   Specht module of [2, 2, 1] over Rational Field
            sage: all(Y.retract(u.lift()) == u for u in Y.basis())
            True

            sage: Y.retract(X.zero())
            0
            sage: Y.retract(sum(X.basis()))
            Traceback (most recent call last):
            ...
            ValueError: ... is not in the image
        """
        B = self.basis()
        COB = matrix([b.lift().to_vector() for b in B]).T
        P, L, U = COB.LU()
        # Since U is upper triangular, the nonzero entriesm must be in the
        #   upper square portiion of the matrix
        n = len(B)

        Uinv = U.matrix_from_rows(range(n)).inverse()
        # This is a slight abuse as the codomain should be a module with a different
        #    S_n action, but we only use it internally, so there isn't any problems
        PLinv = (P*L).inverse()

        def retraction(elt):
            vec = PLinv * elt.to_vector(order=self._support_order)
            if not vec:
                return self.zero()
            # vec is now in the image of self under U, which is
            if max(vec.support()) >= n:
                raise ValueError(f"{elt} is not in the image")
            return self._from_dict(dict(zip(B.keys(), Uinv * vec[:n])))

        return self._ambient.module_morphism(function=retraction, codomain=self)

    def bilinear_form(self, u, v):
        r"""
        Return the natural bilinear form of ``self`` applied to ``u`` and ``v``.

        The natural bilinear form is given by the pullback of the natural
        bilinear form on the tabloid module (where the tabloid basis is an
        orthonormal basis).

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: SM = SGA.specht_module([2,2,1])
            sage: u = SM.an_element(); u
            3*S[[1, 2], [3, 5], [4]] + 2*S[[1, 3], [2, 5], [4]] + 2*S[[1, 4], [2, 5], [3]]
            sage: v = sum(SM.basis())
            sage: SM.bilinear_form(u, v)
            140
        """
        TM = self._ambient
        return TM.bilinear_form(u.lift(), v.lift())

    @cached_method
    def gram_matrix(self):
        r"""
        Return the Gram matrix of the natural bilinear form of ``self``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: SM = SGA.specht_module([2,2,1])
            sage: M = SM.gram_matrix(); M
            [12  4 -4 -4  4]
            [ 4 12  4  4  4]
            [-4  4 12  4  4]
            [-4  4  4 12  4]
            [ 4  4  4  4 12]
            sage: M.det() != 0
            True
        """
        B = self.basis()
        M = matrix([[self.bilinear_form(b, bp) for bp in B] for b in B])
        M.set_immutable()
        return M

    def maximal_submodule(self):
        """
        Return the maximal submodule of ``self``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(GF(3), 5)
            sage: SM = SGA.specht_module([3,2])
            sage: U = SM.maximal_submodule()
            sage: U.dimension()
            4
        """
        return MaximalSpechtSubmodule(self)

    def simple_module(self):
        r"""
        Return the simple (or irreducible) `S_n`-submodule of ``self``.

        .. SEEALSO::

            :class:`~sage.combinat.specht_module.SimpleModule`

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(GF(3), 5)
            sage: SM = SGA.specht_module([3,2])
            sage: L = SM.simple_module()
            sage: L.dimension()
            1

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: SM = SGA.specht_module([3,2])
            sage: SM.simple_module() is SM
            True
        """
        if self.base_ring().characteristic() == 0:
            return self
        return SimpleModule(self)

    Element = SymGroupSpechtModule.Element


class MaximalSpechtSubmodule(Representation_abstract, SubmoduleWithBasis):
    r"""
    The maximal submodule `U^{\lambda, \mu}` of the type `B_n` Specht
    module `S^{\lambda, \mu}`.

    ALGORITHM:

    We construct `U^{(\lambda,\mu)}` as the intersection `S \cap S^{\perp}`,
    where `S^{\perp}` is the orthogonal complement of the Specht module `S`
    inside of the tabloid module `T` (with respect to the natural
    bilinear form on `T`).

    EXAMPLES::

        sage: SGA = SymmetricGroupAlgebra(GF(3), 5)
        sage: SM = SGA.specht_module([3,2])
        sage: U = SM.maximal_submodule()
        sage: u = U.an_element(); u
        2*U[0] + 2*U[1]
        sage: [p * u for p in list(SGA.basis())[:4]]
        [2*U[0] + 2*U[1], 2*U[2] + 2*U[3], 2*U[0] + 2*U[1], U[0] + 2*U[2]]
        sage: sum(SGA.basis()) * u
        0
    """
    def __init__(self, specht_module):
        r"""
        Initialize ``self``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(GF(3), 5)
            sage: SM = SGA.specht_module([3,2])
            sage: U = SM.maximal_submodule()
            sage: TestSuite(U).run()

            sage: SM = SGA.specht_module([2,1,1,1])
            sage: SM.maximal_submodule()
            Traceback (most recent call last):
            ...
            NotImplementedError: only implemented for 3-regular partitions

            sage: SGA = SymmetricGroupAlgebra(QQ, 5)
            sage: SM = SGA.specht_module([3,2])
            sage: U = SM.maximal_submodule()
            sage: TestSuite(U).run()
            sage: U.dimension()
            0
        """
        self._semigroup = specht_module._semigroup
        self._semigroup_algebra = specht_module._semigroup_algebra
        self._side = specht_module._side
        self._left_repr = specht_module._left_repr
        self._right_repr = specht_module._right_repr

        from sage.sets.family import Family
        p = specht_module.base_ring().characteristic()
        if p == 0:
            basis = Family([])
        else:
            TM = specht_module._ambient
            if not all(la.is_regular(p) for la in TM._shape) or (p == 2 and TM._shape[0]):
                basis = specht_module.basis()
            else:
                TV = TM._dense_free_module()
                SV = TV.submodule(specht_module.lift.matrix().columns())
                basis = (SV & SV.complement()).basis()
                basis = [specht_module.retract(TM.from_vector(b)) for b in basis]
                basis = Family(specht_module.echelon_form(basis))

        unitriangular = all(b.leading_support() == 1 for b in basis)
        support_order = list(specht_module.basis().keys())
        cat = specht_module.category().Subobjects()
        SubmoduleWithBasis.__init__(self, basis, support_order, ambient=specht_module,
                                    unitriangular=unitriangular, category=cat,
                                    prefix='U')

    def _repr_(self):
        r"""
        Return a string representation of ``self``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(GF(3), 5)
            sage: SM = SGA.specht_module([3,2])
            sage: SM.maximal_submodule()
            Maximal submodule of Specht module of [3, 2] over Finite Field of size 3
        """
        return f"Maximal submodule of {self._ambient}"

    def _latex_(self):
        r"""
        Return a latex representation of ``self``.

        EXAMPLES::

            sage: B4 = SignedPermutations(4)
            sage: latex(B4.specht_module([[2,1],[1]], GF(3)).maximal_submodule())
            U^{{\def\lr#1{\multicolumn{1}{|@{\hspace{.6ex}}c@{\hspace{.6ex}}|}{\raisebox{-.3ex}{$#1$}}}
            \raisebox{-.6ex}{$\begin{array}[b]{*{2}c}\cline{1-2}
            \lr{\phantom{x}}&\lr{\phantom{x}}\\\cline{1-2}
            \lr{\phantom{x}}\\\cline{1-1}
            \end{array}$}
            },{\def\lr#1{\multicolumn{1}{|@{\hspace{.6ex}}c@{\hspace{.6ex}}|}{\raisebox{-.3ex}{$#1$}}}
            \raisebox{-.6ex}{$\begin{array}[b]{*{1}c}\cline{1-1}
            \lr{\phantom{x}}\\\cline{1-1}
            \end{array}$}
            }}
        """
        from sage.misc.latex import latex
        return "U^{" + ",".join(latex(la) for la in self._shape) + "}"

    Element = SymGroupSpechtModule.Element


class SimpleModule(Representation_abstract, QuotientModuleWithBasis):
    r"""
    The simple `B_n`-module associated with a partition pair `(\lambda, \mu)`.

    The simple module `D^{\lambda, \mu}` is the quotient of the
    Specht module `S^{\lambda, \mu}` by its
    :class:`maximal submodule <MaximalSpechtSubmodule>` `U^{\lambda, \mu}`.

    For `p \neq 2`, a partition pair `(\lambda, \mu)` is `p`-*regular*
    if `\lambda` and `\mu` are `p`-regular partitions. It is `2`-regular
    if `\lambda = \emptyset` and `\mu` is `2`-regular.

    EXAMPLES::

        sage: SGA = SymmetricGroupAlgebra(GF(3), 5)
        sage: SM = SGA.specht_module([3,1,1])
        sage: D = SM.simple_module()
        sage: v = D.an_element(); v
        2*D[[[1, 3, 5], [2], [4]]] + 2*D[[[1, 4, 5], [2], [3]]]
        sage: SGA.an_element() * v
        2*D[[[1, 2, 4], [3], [5]]] + 2*D[[[1, 3, 5], [2], [4]]]

    We give an example on how to construct the decomposition matrix
    (the Specht modules are a complete set of irreducible projective
    modules) and the Cartan matrix of a symmetric group algebra::

        sage: SGA = SymmetricGroupAlgebra(GF(3), 4)
        sage: BM = matrix(SGA.simple_module(la).brauer_character()
        ....:             for la in Partitions(4, regular=3))
        sage: SBT = matrix(SGA.specht_module(la).brauer_character()
        ....:              for la in Partitions(4))
        sage: D = SBT * ~BM; D
        [1 0 0 0]
        [0 1 0 0]
        [1 0 1 0]
        [0 0 0 1]
        [0 0 1 0]
        sage: D.transpose() * D
        [2 0 1 0]
        [0 1 0 0]
        [1 0 2 0]
        [0 0 0 1]

    We verify this against the direct computation (up to reindexing the
    rows and columns)::

        sage: SGA.cartan_invariants_matrix()  # long time
        [1 0 0 0]
        [0 1 0 0]
        [0 0 2 1]
        [0 0 1 2]
    """
    def __init__(self, specht_module):
        r"""
        Initialize ``self``.

        EXAMPLES::

            sage: B4 = SignedPermutations(4)
            sage: TM = B4.tabloid_module([[2,1],[1]], GF(3))
            sage: SM = TM.specht_module()
            sage: SM.dimension()
            8
            sage: SM.maximal_submodule().dimension()
            4
            sage: D = SM.simple_module()
            sage: D
            Simple module of ([2, 1], [1]) over Finite Field of size 3
            sage: D.dimension()
            4
        """
        self._diagram = specht_module._diagram
        p = specht_module.base_ring().characteristic()
        if (not all(la.is_regular(p) for la in specht_module._diagram)
            or (p == 2 and specht_module._diagram[0])):
            raise ValueError(f"the partition must be {p}-regular")
        self._semigroup = specht_module._semigroup
        self._semigroup_algebra = specht_module._semigroup_algebra
        self._side = specht_module._side
        self._left_repr = specht_module._left_repr
        self._right_repr = specht_module._right_repr
        cat = specht_module.category()
        QuotientModuleWithBasis.__init__(self, specht_module.maximal_submodule(), cat, prefix='D')

    def _repr_(self):
        r"""
        Return a string representation of ``self``.

        EXAMPLES::

            sage: SGA = SymmetricGroupAlgebra(GF(3), 5)
            sage: SM = SGA.specht_module([3,1,1])
            sage: SM.simple_module()
            Simple module of [3, 1, 1] over Finite Field of size 3
        """
        return f"Simple module of {self._diagram} over {self.base_ring()}"

    def _latex_(self):
        r"""
        Return a latex representation of ``self``.

        EXAMPLES::

            sage: B4 = SignedPermutations(4)
            sage: latex(B4.simple_module([[2,1],[1]], GF(3)))
            D^{{\def\lr#1{\multicolumn{1}{|@{\hspace{.6ex}}c@{\hspace{.6ex}}|}{\raisebox{-.3ex}{$#1$}}}
            \raisebox{-.6ex}{$\begin{array}[b]{*{2}c}\cline{1-2}
            \lr{\phantom{x}}&\lr{\phantom{x}}\\\cline{1-2}
            \lr{\phantom{x}}\\\cline{1-1}
            \end{array}$}
            },{\def\lr#1{\multicolumn{1}{|@{\hspace{.6ex}}c@{\hspace{.6ex}}|}{\raisebox{-.3ex}{$#1$}}}
            \raisebox{-.6ex}{$\begin{array}[b]{*{1}c}\cline{1-1}
            \lr{\phantom{x}}\\\cline{1-1}
            \end{array}$}
            }}
        """
        from sage.misc.latex import latex
        return "D^{" + ",".join(latex(la) for la in self._shape) + "}"

    Element = SymGroupSpechtModule.Element
