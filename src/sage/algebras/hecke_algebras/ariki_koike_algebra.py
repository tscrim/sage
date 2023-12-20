# sage.doctest: needs sage.combinat sage.modules
r"""
Ariki-Koike Algebras

The *Ariki-Koike algebras* were introduced by Ariki and Koike [AK1994]_ as
a natural generalization of the Iwahori-Hecke algebras of types `A` and `B`
(see :class:`~sage.algebras.iwahori_hecke_algebra.IwahoriHeckeAlgebra`).
Soon afterwards,  Broué and Malle defined analogues of the Hecke
algebras for all complex reflection groups

Fix nonnegative integers `r` an `n`. The Ariki-Koike algebras are
deformations of the group algebra of the complex reflection group
`G(r, 1, n) = \ZZ / r\ZZ \wr \mathfrak{S}_n`. If `R` is a ring containing a
*Hecke parameter* `q` and *cyclotomic parameters* `u_0, \ldots, u_{r-1}` then
the Ariki-Koike algebra `H_n(q, u_1, \ldots, u_r)` is the unital associative
`r`-algebra with generators `T_0, T_1, \ldots, T_{n-1}` an relations:

.. MATH::

    \begin{aligned}
        \prod_{i=0}^{r-1} (T_0 - u_i) & = 0, \\
        T_i^2 & = (q - 1) T_i + q && \text{for } 1 \leq i < n, \\
        T_0 T_1 T_0 T_1 & = T_1 T_0 T_1 T_0, \\
        T_i T_j & = T_j T_i && \text{if } |i - j| \geq 2, \\
        T_i T_{i+1} T_i & = T_{i+1} T_i T_{i+1} && \text{for } 1 \leq i < n.
    \end{aligned}

AUTHORS:

- Travis Scrimshaw (2016-04): initial version
- Andrew Mathas (2016-07): improved multiplication code

REFERENCES:

- [AK1994]_
- [BM1993]_
- [MM1998]_
"""

#*****************************************************************************
#  Copyright (C) 2016-2018 Travis Scrimshaw <tcscrims at gmail.com>
#                2016-2018 Andrew Mathas <andrew.mathas at sydney.edu.au>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************


from sage.misc.cachefunc import cached_method
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.abstract_method import abstract_method
from sage.misc.misc_c import prod
from sage.misc.bindable_class import BindableClass
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation
from sage.categories.algebras import Algebras
from sage.categories.rings import Rings
from sage.categories.realizations import Realizations, Category_realization_of_parent
from sage.categories.cartesian_product import cartesian_product
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.rings.polynomial.laurent_polynomial_ring import LaurentPolynomialRing
from sage.rings.integer_ring import ZZ
from sage.combinat.free_module import CombinatorialFreeModule
from sage.combinat.permutation import Permutations
from sage.combinat.partition_tuple import PartitionTuples
from sage.combinat.tableau_tuple import StandardTableauTuples
from sage.algebras.cellular_basis import CellularBasis
from sage.sets.family import Family
from sage.data_structures.blas_dict import iaxpy


# ABC for basis classes
class _Basis(CombinatorialFreeModule, BindableClass):
    r"""
    Abstract base class for bases of the Ariki-Koike algebra.
    """
    def __init__(self, algebra, prefix='AK'):
        r"""
        Initialize ``self``.

        EXAMPLES::

            sage: LT = algebras.ArikiKoike(2, 3).LT()
            sage: TestSuite(LT).run()
        """
        self._r = algebra._r
        self._n = algebra._n
        self._q = algebra._q
        self._u = algebra._u
        # It seems more efficient to copy this as we need it a lot
        self._zero_tuple = tuple([0] * self._n)
        self._Pn = Permutations(self._n)
        self._one_perm = self._Pn.one()
        C = cartesian_product([range(self._r)] * self._n)
        indices = cartesian_product([C, self._Pn])
        CombinatorialFreeModule.__init__(self, algebra.base_ring(), indices,
                                         prefix=prefix,
                                         category=algebra._BasesCategory())

    @cached_method
    def one_basis(self):
        r"""
        Return the index of the basis element of `1`.

        EXAMPLES::

            sage: LT = algebras.ArikiKoike(5, 3).LT()
            sage: LT.one_basis()
            ((0, 0, 0), [1, 2, 3])

            sage: T = algebras.ArikiKoike(5, 3).T()
            sage: T.one_basis()
            ((0, 0, 0), [1, 2, 3])
        """
        return (self._zero_tuple, self._one_perm)

    @cached_method
    def cell_poset(self):
        """
        Return the cell poset of ``self``.

        EXAMPLES::

            sage: LT = algebras.ArikiKoike(5, 3).LT()
            sage: LT.cell_poset()
            Finite poset containing 65 elements
        """
        from sage.combinat.posets.posets import Poset
        return Poset([PartitionTuples(self._r, self._n), lambda x, y: y.dominates(x)])

    def cell_module_indices(self, la):
        r"""
        Return the indices of the cell module of ``self``
        indexed by ``la`` .

        This is the finite set `M(\lambda)`.

        EXAMPLES::

            sage: LT = algebras.ArikiKoike(5, 3).LT()
            sage: LT.cell_module_indices([[1], [], [1,1], []])
            Standard tableau tuples of shape ([1], [], [1, 1], [])
        """
        return StandardTableauTuples(shape=la)

    def cellular_basis(self):
        r"""
        Return the cellular basis of ``self``.

        EXAMPLES::

            sage: LT = algebras.ArikiKoike(3, 2).LT()
            sage: LT.cellular_basis()
            Cellular basis of Symmetric group algebra of order 3
             over Rational Field
        """
        return self.realization_of().Murphy()


class _CellularBasis(CellularBasis, BindableClass):
    r"""
    Abstract base class for cellular bases of the Ariki-Koike algebra.
    """
    def __init__(self, algebra, **kwds):
        r"""
        Initialize ``self``.

        EXAMPLES::

            sage: M = algebras.ArikiKoike(2, 3).Murphy()
            sage: TestSuite(M).run()  # not tested
        """
        self._r = algebra._r
        self._n = algebra._n
        self._q = algebra._q
        self._u = algebra._u
        CellularBasis.__init__(self, algebra.LT(),
                               to_algebra=self._to_LT,
                               from_algebra=self._from_LT,
                               prefix=self._prefix,
                               category=algebra._BasesCategory(), **kwds)

    @abstract_method(optional=True)
    def _to_LT(self, m):
        r"""
        Convert the basis element indexed by ``m`` from ``self``
        to the LT basis.
        """

    @abstract_method(optional=True)
    def _from_LT(self, m):
        r"""
        Convert the basis element indexed by ``m`` from the LT basis
        to ``self``.
        """

    def _repr_term(self, m):
        return self._prefix + "[{}, {}]".format(m[1]._repr_compact(), m[2]._repr_compact())


class ArikiKoikeAlgebra(Parent, UniqueRepresentation):
    r"""
    The Ariki-Koike algebra `H_{r,n}(q, u)`.

    Let `R` be an unital integral domain.
    Let `q, u_0, \ldots, u_{r-1} \in R` such that `q^{-1} \in R`.
    The *Ariki-Koike algebra* is the unital associative algebra
    `H_{r,n}(q, u)` generated by `T_0, \ldots, T_{n-1}` that satisfies
    the following relations:

    .. MATH::

        \begin{aligned}
            \prod_{i=0}^{r-1} (T_0 - u_i) & = 0, \\
            T_i^2 & = (q - 1) T_i + q && \text{for } 1 \leq i < n, \\
            T_0 T_1 T_0 T_1 & = T_1 T_0 T_1 T_0, \\
            T_i T_j & = T_j T_i && \text{if } |i - j| \geq 2, \\
            T_i T_{i+1} T_i & = T_{i+1} T_i T_{i+1} && \text{for } 1 \leq i < n.
        \end{aligned}

    The parameter `q` is called the *Hecke parameter* and the parameters
    `u_0, \ldots, u_{r-1}` are called the *cyclotomic parameters*.
    Thus, the Ariki-Koike algebra is a deformation of the group algebra of the
    complex reflection group `G(r, 1, n) = \ZZ / r\ZZ \wr \mathfrak{S}_n`.

    Next, we define *Jucys-Murphy elements*

    .. MATH::

        L_i = q^{-i+1} T_{i-1} \cdots T_1 T_0 T_1 \cdots T_{i-1}

    for `1 \leq i \leq n`.

    .. NOTE::

        These element differ by a power of `q` from the corresponding
        elements in [AK1994]_. However, these elements are more commonly
        used because they lead to nicer representation theoretic formulas.

    Ariki and Koike [AK1994]_ showed that `H_{r,n}(q, u)` is a free
    `R`-module with a basis given by

    .. MATH::

        \{ L_1^{c_i} \cdots L_n^{c_n} T_w \mid w \in S_n, 0 \leq c_i < r \}.

    In particular, we have `\dim H_{r,n}(q,u) = r^n n! = |G(r, 1, n)|`.
    Moreover, we have `L_i L_j = L_i L_j` for all `1 \leq i, j \leq n`.

    The Ariki-Koike algebra `H_{r,n}(q, u)` can be considered as a quotient
    of the group algebra of the braid group for `G(r, 1, n)` by the ideal
    generated by `\prod_{i=0}^{r-1} (T_0 - u_i)` and `(T_i - q)(T_i + 1)`.
    Furthermore, `H_{r,n}(q, u)` can be constructed as a quotient of the
    extended affine Hecke algebra of type `A_{n-1}^{(1)}` by
    `\prod_{i=0}^{r-1} (X_1 - u_i)`.

    Since the Ariki-Koike algebra is a quotient of the group
    algebra of the braid group of `G(r, 1, n)`, we can recover
    the group algebra of `G(r, 1, n)` as follows. Consider
    `u = (1, \zeta_r, \ldots, \zeta_r^{r-1})`, where `\zeta_r`
    is a primitive `r`-th root of unity, then we have

    .. MATH::

        R G(r, 1, n) = H_{r,n}(1, u).

    INPUT:

    - ``r`` -- the maximum power of `L_i`
    - ``n`` -- the rank `S_n`
    - ``q`` -- (optional) an invertible element in a commutative ring;
      the default is `q \in R[q,q^{-1}]`, where `R` is the ring containing
      the variables ``u``
    - ``u`` -- (optional) the variables `u_1, \ldots, u_r`; the
      default is the generators of `\ZZ[u_1, \ldots, u_r]`
    - ``R`` -- (optional) a commutative ring containing ``q`` and ``u``;
      the default is the parent of `q` and `u_1, \ldots, u_r`
    - ``use_fraction_field`` -- (default: ``False``) whether to use the
      fraction field or not

    EXAMPLES:

    We start by constructing an Ariki-Koike algebra where the
    values `q, u` are generic and do some computations::

        sage: H = algebras.ArikiKoike(3, 4)

    Next, we do some computations using the `LT` basis::

        sage: LT = H.LT()
        sage: LT.inject_variables()
        Defining L1, L2, L3, L4, T1, T2, T3
        sage: T1 * T2 * T1 * T2
        q*T[2,1] - (1-q)*T[2,1,2]
        sage: T1 * L1 * T2 * L3 * T1 * T2
        -(q-q^2)*L2*L3*T[2] + q*L1*L2*T[2,1] - (1-q)*L1*L2*T[2,1,2]
        sage: L1^3
        u0*u1*u2 + ((-u0*u1-u0*u2-u1*u2))*L1 + ((u0+u1+u2))*L1^2
        sage: L3 * L2 * L1
        L1*L2*L3
        sage: u = LT.u()
        sage: q = LT.q()
        sage: (q + 2*u[0]) * (T1 * T2) * L3
        (-2*u0+(2*u0-1)*q+q^2)*L3*T[1] + (-2*u0+(2*u0-1)*q+q^2)*L2*T[2]
         + (2*u0+q)*L1*T[1,2]

    We check the defining relations::

        sage: prod(L1 - val for val in u) == H.zero()
        True
        sage: L1 * T1 * L1 * T1 == T1 * L1 * T1 * L1
        True
        sage: T1 * T2 * T1 == T2 * T1 * T2
        True
        sage: T2 * T3 * T2 == T3 * T2 * T3
        True
        sage: L2 == q^-1 * T1 * L1 * T1
        True
        sage: L3 == q^-2 * T2 * T1 * L1 * T1 * T2
        True

    We construct an Ariki-Koike algebra with `u = (1, \zeta_3, \zeta_3^2)`,
    where `\zeta_3` is a primitive third root of unity::

        sage: # needs sage.rings.number_field
        sage: F = CyclotomicField(3)
        sage: zeta3 = F.gen()
        sage: R.<q> = LaurentPolynomialRing(F)
        sage: H = algebras.ArikiKoike(3, 4, q=q, u=[1, zeta3, zeta3^2], R=R)
        sage: H.LT().inject_variables()
        Defining L1, L2, L3, L4, T1, T2, T3
        sage: L1^3
        1
        sage: L2^3
        1 - (q^-1-1)*T[1] - (q^-1-1)*L1*L2^2*T[1] - (q^-1-1)*L1^2*L2*T[1]

    Next, we additionally take `q = 1` to obtain the group algebra
    of `G(r, 1, n)`::

        sage: # needs sage.rings.number_field
        sage: F = CyclotomicField(3)
        sage: zeta3 = F.gen()
        sage: H = algebras.ArikiKoike(3, 4, q=1, u=[1, zeta3, zeta3^2], R=F)
        sage: LT = H.LT()
        sage: LT.inject_variables()
        Defining L1, L2, L3, L4, T1, T2, T3
        sage: A = ColoredPermutations(3, 4).algebra(F)
        sage: s1, s2, s3, s0 = list(A.algebra_generators())
        sage: all(L^3 == LT.one() for L in LT.L())
        True
        sage: J = [s0, s3*s0*s3, s2*s3*s0*s3*s2, s1*s2*s3*s0*s3*s2*s1]
        sage: all(Ji^3 == A.one() for Ji in J)
        True
    """
    @staticmethod
    def __classcall_private__(cls, r, n, q=None, u=None, R=None, use_fraction_field=False):
        r"""
        Standardize input to ensure a unique representation.

        TESTS::

            sage: H1 = algebras.ArikiKoike(4, 3)
            sage: S = PolynomialRing(ZZ, 'u', 4)
            sage: R.<q> = LaurentPolynomialRing(S)
            sage: H2 = algebras.ArikiKoike(4, 3, q=q)
            sage: H3 = algebras.ArikiKoike(4, 3, q, S.gens(), R)
            sage: H1 is H2
            True
            sage: H2 is H3
            True
        """
        if u is None:
            if q is not None:
                R = q.parent()
            if R is None:
                R = PolynomialRing(ZZ, 'u', r)
                u = R.gens()
                if q is None:
                    R = LaurentPolynomialRing(R, 'q')
                    q = R.gen()
            else:
                u = PolynomialRing(ZZ, 'u', r).gens()
                if q is None:
                    q = 'q'
        else:
            if not isinstance(u, (list,tuple)):
                u = [u]*r
            if R is None:
                from sage.structure.element import get_coercion_model
                cm = get_coercion_model()
                if q is None:
                    R = cm.common_parent(*[val.parent() for val in u])
                    R = LaurentPolynomialRing(R, 'q')
                    q = R.gen()
                else:
                    R = cm.common_parent(q.parent(), *[val.parent() for val in u])
            elif q is None:
                q = 'q'
        if R not in Rings().Commutative():
            raise TypeError("base ring must be a commutative ring")
        if use_fraction_field:
            R = R.fraction_field()
        q = R(q)
        u = tuple([R(val) for val in u])
        return super().__classcall__(cls, r, n, q, u, R)

    def __init__(self, r, n, q, u, R):
        r"""
        Initialize ``self``.

        EXAMPLES::

            sage: H = algebras.ArikiKoike(5, 3)
            sage: TestSuite(H).run()
            sage: H = algebras.ArikiKoike(1, 4)
            sage: TestSuite(H).run()
            sage: H = algebras.ArikiKoike(2, 3)
            sage: TestSuite(H).run()
            sage: H = algebras.ArikiKoike(3, 4)
            sage: TestSuite(H).run() # long time
        """
        self._r = r
        self._n = n
        self._q = q
        self._u = u
        self._category = Algebras(R).FiniteDimensional().WithBasis().Cellular()
        Parent.__init__(self, base=R, category=self._category.WithRealizations())

        T = self.T()
        LT = self.LT()
        T.module_morphism(LT._from_T_basis, codomain=LT).register_as_coercion()
        LT.module_morphism(T._from_LT_basis, codomain=T).register_as_coercion()

    def _repr_(self):
        r"""
        Return a string representation of ``self``.

        EXAMPLES::

            sage: algebras.ArikiKoike(5, 2)
            Ariki-Koike algebra of rank 5 and order 2
             with q=q and u=(u0, u1, u2, u3, u4)
             over Univariate Laurent Polynomial Ring in q
             over Multivariate Polynomial Ring in u0, u1, u2, u3, u4
             over Integer Ring
        """
        return "Ariki-Koike algebra of rank {} and order {} with q={} and u={} over {}".format(
            self._r, self._n, self._q, self._u, self.base_ring())

    def _latex_(self):
        r"""
        Return a latex representation of ``self``.

        EXAMPLES::

            sage: H = algebras.ArikiKoike(5, 2)
            sage: latex(H)
            \mathcal{H}_{5,2}(q)
        """
        return "\\mathcal{H}_{%s,%s}(%s)" % (self._r, self._n, self._q)

    def hecke_parameter(self):
        r"""
        Return the Hecke parameter `q` of ``self``.

        EXAMPLES::

            sage: H = algebras.ArikiKoike(5, 3)
            sage: H.hecke_parameter()
            q
        """
        return self._q

    q = hecke_parameter

    def cyclotomic_parameters(self):
        r"""
        Return the cyclotomic parameters `u` of ``self``.

        EXAMPLES::

            sage: H = algebras.ArikiKoike(5, 3)
            sage: H.cyclotomic_parameters()
            (u0, u1, u2, u3, u4)
        """
        return self._u

    u = cyclotomic_parameters

    def a_realization(self):
        r"""
        Return a realization of ``self``.

        EXAMPLES::

            sage: H = algebras.ArikiKoike(5, 2)
            sage: H.a_realization()
            Ariki-Koike algebra of rank 5 and order 2
             with q=q and u=(u0, u1, u2, u3, u4) ... in the LT-basis
        """
        return self.LT()

    def specht_module(self, la):
        r"""
        Return the Specht module of ``self`` corresponding to the shape ``la``.

        EXAMPLES::

            sage: AK = algebras.ArikiKoike(4, 6)
            sage: AK.specht_module([[2], [], [1,1,1], [1]])
            Specht module of shape ([2], [], [1, 1, 1], [1]) for
             Ariki-Koike algebra of rank 4 and order 6 with q=q and u=(u0, u1, u2, u3)
             over ... over Integer Ring
        """
        from sage.algebras.hecke_algebras.ariki_koike_specht_modules import SpechtModule
        return SpechtModule(self, la)

    class _BasesCategory(Category_realization_of_parent):
        r"""
        The category of bases of a Ariki-Koike algebra.
        """
        def __init__(self, base):
            r"""
            Initialize ``self``.

            INPUT:

            - ``base`` -- a Ariki-Koike algebra

            TESTS::

                sage: H = algebras.ArikiKoike(5, 2)
                sage: bases = H._BasesCategory()
                sage: H.T() in bases
                True
            """
            Category_realization_of_parent.__init__(self, base)

        def super_categories(self):
            r"""
            The super categories of ``self``.

            EXAMPLES::

                sage: H = algebras.ArikiKoike(5, 2)
                sage: bases = H._BasesCategory()
                sage: bases.super_categories()
                [Category of realizations of Ariki-Koike algebra of rank 5 and order 2
                    with q=q and u=(u0, u1, u2, u3, u4) over ...,
                 Category of finite dimensional algebras with basis over ...]
            """
            return [Realizations(self.base()), self.base()._category]

        def _repr_(self):
            r"""
            Return the representation of ``self``.

            EXAMPLES::

                sage: H = algebras.ArikiKoike(5, 2)
                sage: H._BasesCategory()
                Category of bases of Ariki-Koike algebra of rank 5 and order 2
                 with q=q and u=(u0, u1, u2, u3, u4) over ...
            """
            return "Category of bases of %s" % self.base()

        class ParentMethods:
            r"""
            This class collects code common to all the various bases. In most
            cases, these are just default implementations that will get
            specialized in a basis.
            """
            def _repr_(self):
                r"""
                Text representation of this basis of Iwahori-Hecke algebra.

                EXAMPLES::

                    sage: H = algebras.ArikiKoike(5, 2)
                    sage: H.T()
                    Ariki-Koike algebra of rank 5 and order 2
                     with q=q and u=(u0, u1, u2, u3, u4) ... in the T-basis
                    sage: H.LT()
                    Ariki-Koike algebra of rank 5 and order 2
                     with q=q and u=(u0, u1, u2, u3, u4) ... in the LT-basis
                """
                return "%s in the %s-basis" % (self.realization_of(), self._realization_name())

            def hecke_parameter(self):
                r"""
                Return the Hecke parameter `q` of ``self``.

                EXAMPLES::

                    sage: LT = algebras.ArikiKoike(5, 3).LT()
                    sage: LT.hecke_parameter()
                    q
                """
                return self._q

            q = hecke_parameter

            def cyclotomic_parameters(self):
                r"""
                Return the cyclotomic parameters `u` of ``self``.

                EXAMPLES::

                    sage: LT = algebras.ArikiKoike(5, 3).LT()
                    sage: LT.cyclotomic_parameters()
                    (u0, u1, u2, u3, u4)
                """
                return self._u

            u = cyclotomic_parameters

            @cached_method
            def gens(self):
                r"""
                Return the generators of ``self``.

                EXAMPLES::

                    sage: LT = algebras.ArikiKoike(5, 3).LT()
                    sage: LT.gens()
                    (L1, L2, L3, T[1], T[2])
                """
                return tuple(self.algebra_generators())

            def dimension(self):
                r"""
                Return the dimension of ``self``.

                The dimension of `H_{r,n}(q, u)` is `r^n n!`.

                EXAMPLES::

                    sage: LT = algebras.ArikiKoike(8, 3).LT()
                    sage: LT.dimension()
                    3072
                    sage: LT = algebras.ArikiKoike(6, 3).LT()
                    sage: LT.dimension()
                    1296
                    sage: LT = algebras.ArikiKoike(3, 5).LT()
                    sage: LT.dimension()
                    29160
                """
                from sage.arith.misc import factorial
                return self._r**self._n * factorial(self._n)

            def some_elements(self):
                r"""
                Return a list of elements of ``self``.

                EXAMPLES::

                    sage: LT = algebras.ArikiKoike(4, 3).LT()
                    sage: LT.some_elements()
                    [1 + 2*T[2] + 3*T[1] + T[2,1],
                     L1, L2, L3, T[1], T[2], L1^2, L2^2]
                """
                G = self.algebra_generators()
                elts = [self.an_element()] + list(G)
                elts += [self.L(1)**2]
                if self._n > 1:
                    elts += [self.L(2)**(self._r//2)]
                return elts

            def specht_module(self, la):
                r"""
                Return the Specht module of ``self`` corresponding
                to the shape ``la``.

                EXAMPLES::

                    sage: AK = algebras.ArikiKoike(4, 3)
                    sage: LT = AK.LT()
                    sage: S1 = LT.specht_module([[1], [], [1,1], []])
                    sage: T = AK.T()
                    sage: S2 = T.specht_module([[1], [], [1,1], []])
                    sage: S1 is S2
                    True
                """
                from sage.algebras.hecke_algebras.ariki_koike_specht_modules import SpechtModule
                return SpechtModule(self.realization_of(), la)

            @cached_method(key=lambda s, la: PartitionTuples()(la))
            def central_orthogonal_idempotent(self, la):
                r"""
                Return the central orthogonal idempotent `F_{\lambda}`
                in ``self``.
                """
                la = PartitionTuples(self._r, self._n)(la)
                return self.sum(self.primitive_idempotent(t)
                                for t in StandardTableauTuples(la))

            def central_orthogonal_idempotents(self):
                """
                Return all central orthogonal idempotents of ``self``.
                """
                return [self.central_orthogonal_idempotent(la)
                        for la in PartitionTuples(self._r, self._n)]

            @cached_method(key=lambda s, t: StandardTableauTuples()(t))
            def primitive_idempotent(self, t):
                r"""
                Return the primitive idempotent `F_t` in ``self``.
                """
                t = StandardTableauTuples(self._r, self._n)(t)
                ret = self.one()
                denom = self.base_ring().one()
                q = self._q
                u = self._u
                for k in range(1, self._n+1):
                    res = t.cells_containing(k)[0]
                    if len(res) == 2:  # level 1
                        res = q**(res[1]-res[0]) * u[0]
                    else:
                        res = q**(res[2]-res[1]) * u[res[0]]
                    Lk = self.L(k)
                    for s in range(self._r):
                        for d in range(1-k, k):
                            c = q**d * u[s]
                            if res == c:
                                continue
                            ret *= (Lk - c)
                            denom *= (res - c)
                return ret / denom


        class ElementMethods:
            def trace(self):
                r"""
                Return the trace of ``self``.

                The trace form `\tau` on the Ariki-Koike algebra
                is defined as the coefficient of `1`.
                """
                return self[self.parent().one_basis()]

    # -----------------------------------------------------
    # Basis classes
    # -----------------------------------------------------

    class LT(_Basis):
        r"""
        The basis of the Ariki-Koike algebra given by monomials of the
        form `L T`, where `L` is product of Jucys-Murphy elements and
        `T` is a product of `\{ T_i | 0 < i < n \}`.

        This was the basis defined in [AK1994]_ except using the
        renormalized Jucys-Murphy elements.
        """
        def __init__(self, algebra):
            r"""
            Initialize ``self``.

            EXAMPLES:

            We skip the cellular tests as they require inverting
            a large matrix::

                sage: LT = algebras.ArikiKoike(5, 3).LT()
                sage: TestSuite(LT).run(skip="_test_cellular")
                sage: LT = algebras.ArikiKoike(1, 4).LT()
                sage: TestSuite(LT).run()
                sage: LT = algebras.ArikiKoike(2, 3).LT()
                sage: TestSuite(LT).run(skip="_test_cellular")
                sage: LT = algebras.ArikiKoike(3, 4).LT()
                sage: TestSuite(LT).run(skip="_test_cellular")  # long time
            """
            _Basis.__init__(self, algebra, prefix='LT')
            self._assign_names(self.algebra_generators().keys())

        def _repr_term(self, m):
            r"""
            Return a string representation of the basis element indexed by ``m``.

            EXAMPLES::

                sage: LT = algebras.ArikiKoike(4, 3).LT()
                sage: LT._repr_term( ((1, 0, 2), Permutation([3,2,1])) )
                'L1*L3^2*T[2,1,2]'
            """
            gen_str = lambda e: '' if e == 1 else '^%s' % e
            lhs = '*'.join('L%s' % (j+1) + gen_str(i)
                           for j,i in enumerate(m[0]) if i > 0)
            redword = m[1].reduced_word()
            if not redword:
                if not lhs:
                    return '1'
                return lhs
            rhs = 'T[{}]'.format(','.join(str(i) for i in redword))
            if not lhs:
                return rhs
            return lhs + '*' + rhs

        def _latex_term(self, m):
            r"""
            Return a latex representation for the basis element indexed by ``m``.

            EXAMPLES::

                sage: LT = algebras.ArikiKoike(4, 3).LT()
                sage: LT._latex_term( ((1, 0, 2), Permutation([3,2,1])) )
                'L_{1} L_{3}^{2} T_{2} T_{1} T_{2}'
            """
            gen_str = lambda e: '' if e == 1 else '^{%s}' % e
            lhs = ' '.join('L_{%s}' % (j+1) + gen_str(i)
                           for j,i in enumerate(m[0]) if i > 0)
            redword = m[1].reduced_word()
            if not redword:
                if not lhs:
                    return '1'
                return lhs
            return lhs + ' ' + ' '.join("T_{%d}" % i for i in redword)

        def _from_T_basis(self, t):
            r"""
            Return the image of the `T` basis element indexed
            by ``t`` in ``self``.

            EXAMPLES::

                sage: H = algebras.ArikiKoike(3, 3)
                sage: LT = H.LT()
                sage: T = H.T()
                sage: all(LT(Li) == LT.L(i+1) for i,Li in enumerate(T.L()))
                True
                sage: all(LT(Ti) == LT.T(i) for i,Ti in enumerate(T.T()))
                True
                sage: all(LT(T(b)) == b for b in LT.basis())  # long time
                True

                sage: H = algebras.ArikiKoike(1, 3)
                sage: LT = H.LT()
                sage: T = H.T()
                sage: all(LT(Li) == LT.L(i+1) for i,Li in enumerate(T.L()))
                True
                sage: all(LT(T(b)) == b for b in LT.basis())  # indirect doctest
                True
            """
            # Compute the corresponding reduced word for the first part
            ret = self.one()
            T = list(self._zero_tuple)
            one = self.base_ring().one()
            for i,k in enumerate(t[0]):
                if k == 0:
                    continue
                perm = self._Pn.prod(self._Pn.simple_reflection(j)
                                     for j in range(1,i+1))
                ret = ret * self._from_dict({(self._zero_tuple, perm): one},
                                            remove_zeros=False, coerce=False)
                T[0] = k
                ret = ret * self._from_dict({(tuple(T), self._one_perm): one},
                                            remove_zeros=False, coerce=False)

            return ret * self._from_dict({(self._zero_tuple, t[1]): one},
                                         remove_zeros=False, coerce=False)

        @cached_method
        def algebra_generators(self):
            r"""
            Return the algebra generators of ``self``.

            EXAMPLES::

                sage: LT = algebras.ArikiKoike(5, 3).LT()
                sage: dict(LT.algebra_generators())
                {'L1': L1, 'L2': L2, 'L3': L3, 'T1': T[1], 'T2': T[2]}

                sage: LT = algebras.ArikiKoike(1, 4).LT()
                sage: dict(LT.algebra_generators())
                {'T1': T[1], 'T2': T[2], 'T3': T[3]}
            """
            d = {}
            if self._r != 1:
                for i in range(self._n):
                    r = list(self._zero_tuple) # Make a copy
                    r[i] = 1
                    d['L%s' % (i+1)] = self.monomial( (tuple(r), self._one_perm) )
            G = self._Pn.group_generators()
            for i in range(1, self._n):
                d['T%s' % i] = self.monomial( (self._zero_tuple, G[i]) )
            return Family(sorted(d), lambda i: d[i])

        def T(self, i=None):
            r"""
            Return the generator(s) `T_i` of ``self``.

            INPUT:

            - ``i`` -- (default: ``None``) the generator `T_i` or
              if ``None``, then the list of all generators `T_i`

            EXAMPLES::

                sage: LT = algebras.ArikiKoike(8, 3).LT()
                sage: LT.T(1)
                T[1]
                sage: LT.T()
                [L1, T[1], T[2]]
                sage: LT.T(0)
                L1

                sage: LT = algebras.ArikiKoike(1, 3).LT()
                sage: LT.T()
                [u, T[1], T[2]]
                sage: LT.T(0)
                u
            """
            G = self.algebra_generators()
            if i is None:
                return [self.L(1)] + [G['T%s' % j] for j in range(1, self._n)]
            if i == 0:
                return G[self.L(1)]
            return G['T%s' % i]

        def L(self, i=None):
            r"""
            Return the generator(s) `L_i`.

            INPUT:

            - ``i`` -- (default: ``None``) the generator `L_i` or
              if ``None``, then the list of all generators `L_i`

            EXAMPLES::

                sage: LT = algebras.ArikiKoike(8, 3).LT()
                sage: LT.L(2)
                L2
                sage: LT.L()
                (L1, L2, L3)

                sage: LT = algebras.ArikiKoike(1, 3).LT()
                sage: LT.L(2)
                u + (-u*q^-1+u)*T[1]
                sage: LT.L()
                (u,
                 u + (-u*q^-1+u)*T[1],
                 u + (-u*q^-1+u)*T[2] + (-u*q^-2+u*q^-1)*T[2,1,2])
            """
            G = self.algebra_generators()
            if i is None:
                if self._r == 1:
                    return tuple([self._Li_power(j, 1) for j in range(1, self._n+1)])
                return tuple([G['L%s' % j] for j in range(1, self._n+1)])
            if self._r == 1:
                return self._Li_power(i, 1)
            return G['L%s' % i]

        @cached_method
        def product_on_basis(self, m1, m2):
            r"""
            Return the product of the basis elements indexed
            by ``m1`` and ``m2``.

            EXAMPLES::

                sage: LT = algebras.ArikiKoike(6, 3).LT()
                sage: m = ((1, 0, 2), Permutations(3)([2,1,3]))
                sage: LT.product_on_basis(m, m)
                q*L1*L2*L3^4

                sage: LT = algebras.ArikiKoike(4, 3).LT()
                sage: L1,L2,L3,T1,T2 = LT.algebra_generators()
                sage: L1 * T1 * L1^2 * T1
                q*L1*L2^2 + (1-q)*L1^2*L2*T[1]
                sage: L1^2 * T1 * L1^2 * T1
                q*L1^2*L2^2 + (1-q)*L1^3*L2*T[1]
                sage: L1^3 * T1 * L1^2 * T1
                (-u0*u1*u2*u3+u0*u1*u2*u3*q)*L2*T[1]
                 + ((u0*u1*u2+u0*u1*u3+u0*u2*u3+u1*u2*u3)+(-u0*u1*u2-u0*u1*u3-u0*u2*u3-u1*u2*u3)*q)*L1*L2*T[1]
                 + ((-u0*u1-u0*u2-u1*u2-u0*u3-u1*u3-u2*u3)+(u0*u1+u0*u2+u1*u2+u0*u3+u1*u3+u2*u3)*q)*L1^2*L2*T[1]
                 + ((u0+u1+u2+u3)+(-u0-u1-u2-u3)*q)*L1^3*L2*T[1] + q*L1^3*L2^2

                sage: L1^2 * T1 * L1^3 * T1
                (-u0*u1*u2*u3+u0*u1*u2*u3*q)*L2*T[1]
                 + ((u0*u1*u2+u0*u1*u3+u0*u2*u3+u1*u2*u3)+(-u0*u1*u2-u0*u1*u3-u0*u2*u3-u1*u2*u3)*q)*L1*L2*T[1]
                 + ((-u0*u1-u0*u2-u1*u2-u0*u3-u1*u3-u2*u3)+(u0*u1+u0*u2+u1*u2+u0*u3+u1*u3+u2*u3)*q)*L1^2*L2*T[1]
                 + q*L1^2*L2^3
                 + ((u0+u1+u2+u3)+(-u0-u1-u2-u3)*q)*L1^3*L2*T[1]
                 + (1-q)*L1^3*L2^2*T[1]

                sage: L1^2 * T1*T2*T1 * L2 * L3 * T2
                (q-2*q^2+q^3)*L1^2*L2*L3 - (1-2*q+2*q^2-q^3)*L1^2*L2*L3*T[2]
                 - (q-q^2)*L1^3*L3*T[1] + (1-2*q+q^2)*L1^3*L3*T[1,2]
                 + q*L1^3*L2*T[2,1] - (1-q)*L1^3*L2*T[2,1,2]

                sage: LT = algebras.ArikiKoike(2, 3).LT()
                sage: L3 = LT.L(3)
                sage: x = LT.an_element()
                sage: (x * L3) * L3 == x * (L3 * L3)
                True
            """
            # Although it is tempting to make this recursive, some care must be
            #   taken here to ensure that the various "helper" methods return
            #   linear combinations of "standard" basis elements of the form
            #   (L,w), where L is an n-tuple and w is a permutation because
            #   otherwise we may end up in an infinite loop...

            # Product is of the form L1*T1*L2*T2: separate the L's and permutations
            L1,T1 = m1
            L2,T2 = m2

            if sum(L2) == 0:
                # Compute and return the product of T1 and T2, whilst fixing L
                return self._from_dict(self._product_LTwTv(L1, T1, T2),
                                       remove_zeros=False, coerce=False)

            # If T1 is trivial then we just have L1*L2*T2 we only need to rewrite
            # all of the "large" powers that appear in L1*L2. Unfortunately, this
            # will almost certainly introduce more T_w's and it will be recursive
            # because L_n^r, for example, will introduce many powers of L_k for k<n.
            if T1 == self._one_perm:
                Lbig = list(self._zero_tuple)   # separate the "big" and small
                Lsmall = list(self._zero_tuple) # powers of the Lk's
                for i in range(self._n):
                    s = L1[i] + L2[i]
                    if s < self._r:
                        Lsmall[i] = s
                    else:
                        Lbig[i] = s
                if tuple(Lbig) == self._zero_tuple:
                    # if no big powers we only need to combine Lsmall and T2
                    return self.monomial((tuple(Lsmall), T2))

                # The l variables all commute, so we can multiply them in any order
                # that we like. For improved efficiency, however, we move the Ls to
                # the left as soon as we can. For efficiency, we multiply the
                # "big" powers in the order L_n^N L_{n-1}^N...L_1^N as this
                # way we have to expand few powers the of the Lk's later.
                return (self.monomial((tuple(Lsmall), self._one_perm))
                        * prod(self._Li_power(i+1, Lbig[i])
                               for i in reversed(range(self._n)) if Lbig[i] > 0)
                        * self.monomial((self._zero_tuple, T2))
                        )

            # If we are still here then both T1 and L2 are non-trivial. Using the
            # method _product_Tw_L we expand the product T1*L2 as a linear
            # combination of standard basis elements using the method and then,
            # recursively, multiply on the left and right by L1 and T2,
            # respectively. In other words, we multiply as L1*(T1*L2)*T2.
            return ( self.monomial((L1, self._one_perm))
                     * self._product_Tw_L(T1, L2)
                     * self.monomial((self._zero_tuple, T2)) )

        def _product_LTwTv(self, L, w, v):
            r"""
            Return the product `L * T_w * Tv` as a linear combinations of
            terms of the form `L*T_x`.

            The main point of this method is that it computes the product
            `L T_w T_v` and returns it as a linear combination of standard
            basis elements. That is, terms of the form `L T_x`. The monomial
            ``L`` does not play a role in this calculation and, instead, it
            is kept as a place holder for this "L-component" of the product.

            For this calculation the most important point is that

            .. MATH::

                T_i T_v = \begin{cases}
                    T_{s_i v},              & \text{if } \ell(s_iv) > \ell(v),\\
                    q T_{s_i v} + (q-1)T_v, & \text{if } \ell(s_iv) < \ell(v).
                \end{cases}

            This observation is used to rewrite the product `L T_w T_v`
            as a linear combination of standard basis elements.

            .. WARNING::

                This method is not intended to be called directly and, instead,
                is used by :meth:`product_on_basis`.

            INPUT:

            - ``L`` -- an `n`-tuple
            - ``w`` -- the permutation ``w``
            - ``v`` -- the permutation ``v``

            OUTPUT: the corresponding element represented as a ``dict``

            EXAMPLES::

                sage: H = algebras.ArikiKoike(5, 4).LT()
                sage: P4 = Permutations(4)
                sage: H._from_dict( H._product_LTwTv((0, 3, 2, 4), P4([1,3,2,4]), P4([1,3,2,4])) )
                q*L2^3*L3^2*L4^4 - (1-q)*L2^3*L3^2*L4^4*T[2]
                sage: H._from_dict( H._product_LTwTv((0, 3, 2, 4), P4([1,3,2,4]), P4([1,3,4,2])) )
                q*L2^3*L3^2*L4^4*T[3] - (1-q)*L2^3*L3^2*L4^4*T[2,3]
                sage: H._from_dict( H._product_LTwTv((0, 3, 2, 4), P4([1,4,3,2]), P4([1,4,3,2])) )
                q^3*L2^3*L3^2*L4^4 - (q^2-q^3)*L2^3*L3^2*L4^4*T[3]
                 - (q^2-q^3)*L2^3*L3^2*L4^4*T[2]
                 + (q-2*q^2+q^3)*L2^3*L3^2*L4^4*T[2,3]
                 + (q-2*q^2+q^3)*L2^3*L3^2*L4^4*T[3,2]
                 - (1-2*q+2*q^2-q^3)*L2^3*L3^2*L4^4*T[3,2,3]
            """
            ret = {v: self.base_ring().one()}
            qm1 = self._q - self.base_ring().one()
            for i in reversed(w.reduced_word()):
                temp = {} # start from 0
                for p in ret:
                    c = ret[p]
                    # We have to flip the side due to Sage's
                    # convention for multiplying permutations
                    pi = p.apply_simple_reflection(i, side='left')
                    if p.has_descent(i, side='left'):
                        iaxpy(1, {p: c * qm1, pi: c * self._q}, temp)
                    else:
                        iaxpy(1, {pi: c}, temp)
                ret = temp
            return {(L, p): ret[p] for p in ret}

        def _product_Tw_L(self, w, L):
            r"""
            Given a permutation ``w`` and a monomial ``L`` return the product
            `T_w L` as a linear combination of terms of the form `L_v T_v`.

            To do this we write `w = s_{i_1} \cdots s_{i_k}` and then push each
            `T_{i_a}` past `L` using Lemma 3.2 of [MM1998]_ (cf. Lemma 3.3 and
            Proposition 3.4 of [AK1994]_), which says

            .. MATH::

                T_i L_i^a L_{i+1}^b = L_i^b L_{i+1}^a T_i + \begin{cases}
                  (1-q) sum_{k=0}^{a-1} L_i^{a+k} L_{i+1}^{b-k}, &\text{if } a \leq b,\\
                  (q-1) sum_{k=0}^{b-1} L_i^{b+k} L_{i+1}^{a-k}, &\text{if } a \geq b.
                \end{cases}

            Of course, `T_i` commutes with `L_k`, for `k \neq i,i+1`.

            This method is not intended to be called directly and, instead,
            is used by :meth:`product_on_basis`.

            INPUT:

            - ``w`` -- a permutation
            - ``L`` -- tuple `(a_1, \ldots, a_n)`

            EXAMPLES::

                sage: H = algebras.ArikiKoike(5, 4).LT()
                sage: P4 = Permutations(4)
                sage: H._product_Tw_L(P4([1,3,2,4]), (0,2,2,0))
                L2^2*L3^2*T[2]
                sage: H._product_Tw_L(P4([1,3,2,4]), (0,1,3,0))
                -(1-q)*L2*L3^3 - (1-q)*L2^2*L3^2 + L2^3*L3*T[2]
                sage: H._product_Tw_L(P4([1,3,2,4]), (0,3,1,0))
                (1-q)*L2*L3^3 + L2*L3^3*T[2] + (1-q)*L2^2*L3^2
                sage: H._product_Tw_L(P4([1,3,2,4]), (2,3,1,3))
                (1-q)*L1^2*L2*L3^3*L4^3 + L1^2*L2*L3^3*L4^3*T[2] + (1-q)*L1^2*L2^2*L3^2*L4^3
            """
            # initialize wL to L: this is what we will eventually return
            wL = {(L, self._one_perm): self.base_ring().one()}
            q = self._q
            one = q.parent().one()
            for i in w.reduced_word()[::-1]:
                iL = {} # this will become T_i * L, written in standard form
                for lv in wL:
                    c = wL[lv]
                    L = list(lv[0]) # make a copy
                    v = lv[1]
                    a, b = L[i-1], L[i]
                    L[i-1], L[i] = L[i], L[i-1] # swap L_i=L[i-1] and L_{i+1}=L[i]
                    # the term L_1^{a_1} ... L_i^{a_{i+1}} L_{i+1}^{a_i} ... L_n^{a_n} T_i T_v
                    # always appears
                    iaxpy(c, self._product_LTwTv(tuple(L), self._Pn.simple_reflections()[i], v), iL) # need T_i*T_v

                    if a < b:
                        Ls = [ list(L) for k in range(b-a) ] # make copies of L
                        for k in range(b-a):
                            Ls[k][i-1] = a + k
                            Ls[k][i] = b - k
                        c *= (q - one)
                        iaxpy(1, {(tuple(l), v): c for l in Ls}, iL)

                    elif a > b:
                        Ls = [ list(L) for k in range(a-b) ] # make copies of L
                        for k in range(a-b):
                            Ls[k][i-1] = b + k
                            Ls[k][i] = a - k
                        c *= (one - q)
                        iaxpy(1, {(tuple(l), v): c for l in Ls}, iL)

                wL = iL # replace wL with iL and repeat
            return self._from_dict(wL, remove_zeros=False, coerce=False)

        @cached_method
        def _Li_power(self, i, m):
            r"""
            Return `L_i^m`, where `m \geq 0`.

            To compute `L_i^m` we use Corollary 3.4 of [MM1998]_ which says that

            .. MATH::

                L_i^m = q^{-1} T_{i-1} L_{i-1}^m T_{i-1}
                  + (1 - q^{-1}) \sum_{c=1}^{m-1} L_i^c L_{i-1}^{m-c} T_{i-1}.

            .. WARNING::

                This function is used internally by the multiplication and
                may return elements that are not in the basis. However
                these will be eventually resolved after the product has
                been computed. ::

                    sage: H = algebras.ArikiKoike(3, 2).LT()
                    sage: L2 = H.L(2)
                    sage: H._Li_power(2, 4)
                    ((u0^2*u1*u2+u0*u1^2*u2+u0*u1*u2^2)) + ...
                     - (q^-1-1)*L1*L2^3*T[1] ...
                     - (q^-1-1)*L1^3*L2*T[1]
                    sage: H._Li_power(2, 4) == L2^4
                    False
                    sage: L2 * H._Li_power(2, 4) == L2^5
                    True

            EXAMPLES::

                sage: H = algebras.ArikiKoike(3, 3).LT()
                sage: for i in range(1,4):
                ....:     for m in range(4):
                ....:         print('L_{}^{} = {}'.format(i,m,H._Li_power(i,m)))
                L_1^0 = 1
                L_1^1 = L1
                L_1^2 = L1^2
                L_1^3 = u0*u1*u2 + ((-u0*u1-u0*u2-u1*u2))*L1 + ((u0+u1+u2))*L1^2
                L_2^0 = 1
                L_2^1 = L2
                L_2^2 = L2^2
                L_2^3 = u0*u1*u2 + (-u0*u1*u2*q^-1+u0*u1*u2)*T[1]
                 + ((-u0*u1-u0*u2-u1*u2))*L2 + ((u0+u1+u2))*L2^2
                 + ((u0+u1+u2)*q^-1+(-u0-u1-u2))*L1*L2*T[1]
                 - (q^-1-1)*L1*L2^2*T[1] - (q^-1-1)*L1^2*L2*T[1]
                L_3^0 = 1
                L_3^1 = L3
                L_3^2 = L3^2
                L_3^3 = u0*u1*u2 + (-u0*u1*u2*q^-1+u0*u1*u2)*T[2]
                + (-u0*u1*u2*q^-2+u0*u1*u2*q^-1)*T[2,1,2]
                + ((-u0*u1-u0*u2-u1*u2))*L3 + ((u0+u1+u2))*L3^2
                + ((u0+u1+u2)*q^-1+(-u0-u1-u2))*L2*L3*T[2]
                - (q^-1-1)*L2*L3^2*T[2] - (q^-1-1)*L2^2*L3*T[2]
                + ((u0+u1+u2)*q^-2+(-2*u0-2*u1-2*u2)*q^-1+(u0+u1+u2))*L1*L3*T[1,2]
                + ((u0+u1+u2)*q^-2+(-u0-u1-u2)*q^-1)*L1*L3*T[2,1,2]
                - (q^-2-2*q^-1+1)*L1*L3^2*T[1,2] - (q^-2-q^-1)*L1*L3^2*T[2,1,2]
                - (q^-2-2*q^-1+1)*L1*L2*L3*T[1,2] - (q^-2-2*q^-1+1)*L1^2*L3*T[1,2]
                - (q^-2-q^-1)*L1^2*L3*T[2,1,2]
            """
            # shorthand for returning a tuple of the form (0,...,a,b,...,0) with a,b
            # in the (i-1)th and i-th positions, respectively
            def Ltuple(a, b):
                return tuple([b if j == i else a if j == i-1 else 0
                              for j in range(1,self._n+1)])

            # return "small" powers of the generators without change
            if m < self._r:
                return self.monomial( (Ltuple(0, m), self._one_perm) )

            if i > 1:
                si = self._Pn.simple_reflections()[i-1]
                qsum = self.base_ring().one() - self._q**-1
                # by calling _Li_power we avoid infinite recursion here
                return ( self.sum_of_terms( ((Ltuple(c, m-c), si), qsum) for c in range(1, m) )
                         + self._q**-1 * self.T(i-1) * self._Li_power(i-1, m) * self.T(i-1) )

            # now left with the case i = 1 and m >= r
            if m > self._r:
                return self.monomial((Ltuple(0, 1), self._one_perm)) * self._Li_power(i,m-1)

            z = PolynomialRing(self.base_ring(), 'DUMMY').gen()
            p = list(prod(z - val for val in self._u))#[:-1]
            p.pop() # remove the highest power
            zero = self.base_ring().zero()
            return self._from_dict({(Ltuple(0, exp), self._one_perm): -coeff
                                    for exp,coeff in enumerate(p) if coeff != zero},
                                   remove_zeros=False, coerce=False)

        @cached_method
        def inverse_T(self, i):
            r"""
            Return the inverse of the generator `T_i`.

            From the quadratic relation, we have

            .. MATH::

                T_i^{-1} = q^{-1} T_i + (q^{-1} - 1).

            EXAMPLES::

                sage: LT = algebras.ArikiKoike(3, 4).LT()
                sage: [LT.inverse_T(i) for i in range(1, 4)]
                [(q^-1-1) + (q^-1)*T[1],
                 (q^-1-1) + (q^-1)*T[2],
                 (q^-1-1) + (q^-1)*T[3]]

            TESTS::

                sage: LT = algebras.ArikiKoike(4, 4).LT()
                sage: all(LT.inverse_T(i) * LT.T(i) == LT.one() for i in range(1, 4))
                True
                sage: all(LT.T(i) * LT.inverse_T(i) == LT.one() for i in range(1, 4))
                True
            """
            c = ~self._q - self.base_ring().one()
            m = self.T(i).leading_support()
            return self._from_dict({m: ~self._q, self.one_basis(): c})

        def cellular_involution(self, m):
            """
            Return the cellular involution of the basis element indexed by
            ``m`` in ``self``.
            """
            T = self.T()
            return self.prod(T[i] for i in reversed(m[1].reduced_word())) * self.monomial((m[0], self._one_perm))

        class Element(CombinatorialFreeModule.Element):
            def __invert__(self):
                r"""
                Return the inverse if ``self`` is a basis element.

                EXAMPLES::

                    sage: LT = algebras.ArikiKoike(3, 4).LT()
                    sage: t = LT.T(1) * LT.T(2) * LT.T(3); t
                    T[1,2,3]
                    sage: t.inverse()   # indirect doctest
                    (q^-3-3*q^-2+3*q^-1-1) + (q^-3-2*q^-2+q^-1)*T[3]
                     + (q^-3-2*q^-2+q^-1)*T[2] + (q^-3-q^-2)*T[3,2]
                     + (q^-3-2*q^-2+q^-1)*T[1] + (q^-3-q^-2)*T[1,3]
                     + (q^-3-q^-2)*T[2,1] + (q^-3)*T[3,2,1]
                """
                if len(self) != 1:
                    raise NotImplementedError("inverse only implemented for monomials")
                l,w = self.support_of_term()
                if sum(l) != 0:
                    raise NotImplementedError("inverse only implemented for monomials in T variables")
                H = self.parent()
                return ~self[l,w] * H.prod(H.inverse_T(i) for i in reversed(w.reduced_word()))

    class T(_Basis):
        r"""
        The basis of the Ariki-Koike algebra given by monomials of the
        generators `\{ T_i | 0 \leq i < n \}`.

        We use the choice of reduced expression given by [BM1997]_:

        .. MATH::

            T_{1,a_1} \cdots T_{n,a_n} T_w,

        where `T_{i,k} = T_{i-1} \cdots T_2 T_1 T_0^k` (note that
        `T_{1,k} = T_0^k`) and `w` is a reduced expression of an
        element in `\mathfrak{S}_n`.
        """
        def __init__(self, algebra):
            r"""
            Initialize ``self``.

            EXAMPLES:

            We skip the cellular tests as they require inverting
            a large matrix::

                sage: T = algebras.ArikiKoike(5, 3).T()
                sage: TestSuite(T).run(skip="_test_cellular")
                sage: T = algebras.ArikiKoike(1, 4).T()
                sage: TestSuite(T).run()
                sage: T = algebras.ArikiKoike(2, 3).T()
                sage: TestSuite(T).run(skip="_test_cellular")
                sage: T = algebras.ArikiKoike(3, 4).T()
                sage: TestSuite(T).run(skip="_test_cellular") # long time
            """
            _Basis.__init__(self, algebra, prefix='T')
            self._assign_names(['T%s' % i for i in range(self._n)])

        def _basis_to_word(self, t):
            """
            Return the basis element indexed by ``m`` to a word.
            """
            redword = []
            for i, k in enumerate(t[0]):
                if not k:
                    continue
                redword.extend(list(range(i, 0, -1)) + [0]*k)
            redword.extend(t[1].reduced_word())
            return redword

        def _repr_term(self, t):
            r"""
            Return a string representation of the basis element indexed by ``m``.

            EXAMPLES::

                sage: T = algebras.ArikiKoike(4, 3).T()
                sage: T._repr_term( ((1,0,2), Permutation([3,2,1])) )
                'T[0,2,1,0,0,2,1,2]'
            """
            redword = self._basis_to_word(t)
            if not redword:
                return "1"
            return (self._print_options['prefix']
                    + '[%s]' % ','.join('%d' % i for i in redword))

        def _latex_term(self, t):
            r"""
            Return a latex representation for the basis element indexed by ``m``.

            EXAMPLES::

                sage: T = algebras.ArikiKoike(4, 3).T()
                sage: T._latex_term( ((1,0,2), Permutation([3,2,1])) )
                'T_{0}T_{2}T_{1}T_{0}T_{0}T_{2}T_{1}T_{2}'
            """
            redword = self._basis_to_word(t)
            if not redword:
                return "1"
            return ''.join("%s_{%d}" % (self._print_options['prefix'], i)
                           for i in redword)

        def _from_LT_basis(self, m):
            r"""
            Return the image of the `LT` basis element indexed
            by ``m`` in ``self``.

            EXAMPLES::

                sage: H = algebras.ArikiKoike(4, 2)
                sage: LT = H.LT()
                sage: T = H.T()
                sage: all(T(Li) == T.L(i+1) for i,Li in enumerate(LT.L()))
                True
                sage: all(T(Ti) == T.T(i) for i,Ti in enumerate(LT.T()))
                True

            Check that the products of elements agrees::

                sage: type_A_words = [p.reduced_word() for p in Permutations(H._n)]
                sage: def from_reduced_word(B, w):
                ....:     t = B.T()
                ....:     return B.prod(t[i] for i in w)
                sage: all(T(from_reduced_word(LT, w)) == from_reduced_word(T, w)
                ....:     for w in type_A_words)
                True

            Check that the composition of the morphisms is the identity::

                sage: all(T(LT(b)) == b for b in T.basis())  # indirect doctest
                True
            """
            ret = self.prod(self.L(i+1)**k for i,k in enumerate(m[0]))
            return ret * self.monomial( (self._zero_tuple, m[1]) )

        @cached_method
        def algebra_generators(self):
            r"""
            Return the algebra generators of ``self``.

            EXAMPLES::

                sage: T = algebras.ArikiKoike(5, 3).T()
                sage: dict(T.algebra_generators())
                {0: T[0], 1: T[1], 2: T[2]}

                sage: T = algebras.ArikiKoike(1, 4).T()
                sage: dict(T.algebra_generators())
                {1: T[1], 2: T[2], 3: T[3]}
            """
            start = 1 if self._r == 1 else 0
            return Family(list(range(start, self._n)), self.T)

        def T(self, i=None):
            r"""
            Return the generator(s) `T_i` of ``self``.

            INPUT:

            - ``i`` -- (default: ``None``) the generator `T_i` or if ``None``,
              then the list of all generators `T_i`

            EXAMPLES::

                sage: T = algebras.ArikiKoike(8, 3).T()
                sage: T.T(1)
                T[1]
                sage: T.T()
                [T[0], T[1], T[2]]

                sage: T = algebras.ArikiKoike(1, 4).T()
            """
            if i is None:
                return [self.T(j) for j in range(self._n)]

            if i == 0:
                return self.monomial( ((1,) + self._zero_tuple[1:], self._one_perm) )
            s = self._Pn.simple_reflections()
            return self.monomial( (self._zero_tuple, s[i]) )

        @cached_method
        def L(self, i=None):
            r"""
            Return the Jucys-Murphy element(s) `L_i`.

            The Jucys-Murphy element `L_i` is defined as

            .. MATH::

                L_i = q^{-i+1} T_{i-1} \cdots T_1 T_0 T_1 \cdots T_{i-1}
                = q^{-1} T_{i-1} L_{i-1} T_{i-1}.

            INPUT:

            - ``i`` -- (default: ``None``) the Jucys-Murphy element `L_i`
              or if ``None``, then the list of all `L_i`

            EXAMPLES::

                sage: T = algebras.ArikiKoike(8, 3).T()
                sage: T.L(2)
                (q^-1)*T[1,0,1]
                sage: T.L()
                (T[0], (q^-1)*T[1,0,1], (q^-2)*T[2,1,0,1,2])

                sage: T0,T1,T2 = T.T()
                sage: q = T.q()
                sage: T.L(1) == T0
                True
                sage: T.L(2) == q^-1 * T1*T0*T1
                True
                sage: T.L(3) == q^-2 * T2*T1*T0*T1*T2
                True

                sage: T = algebras.ArikiKoike(1, 3).T()
                sage: T.L(2)
                u + (-u*q^-1+u)*T[1]
                sage: T.L()
                (u,
                 u + (-u*q^-1+u)*T[1],
                 u + (-u*q^-1+u)*T[2] + (-u*q^-2+u*q^-1)*T[2,1,2])

            TESTS:

            Check that the Jucys-Murphy elements form a commutative
            subring::

                sage: T = algebras.ArikiKoike(8, 4).T()
                sage: L = T.L()
                sage: all(x*y == y*x for x in L for y in L)
                True

                sage: T = algebras.ArikiKoike(2, 3).T()
                sage: L = T.L()
                sage: all(x*y == y*x for x in L for y in L)
                True

                sage: T = algebras.ArikiKoike(1, 4).T()
                sage: L = T.L()
                sage: all(x*y == y*x for x in L for y in L)
                True
            """
            if i is None:
                return tuple([self.L(j) for j in range(1, self._n+1)])

            if i == 1:
                if self._r == 1:
                    return self.from_base_ring(self._u[0])
                else:
                    return self.T(0)
            T = self.T()
            return self._q**-1 * T[i-1] * self.L(i-1) * T[i-1]

        @cached_method
        def product_on_basis(self, m1, m2):
            r"""
            Return the product of the basis elements indexed
            by ``m1`` and ``m2``.

            EXAMPLES::

                sage: T = algebras.ArikiKoike(2, 3).T()
                sage: T0, T1, T2 = T.T()
                sage: T.product_on_basis(T0.leading_support(), T1.leading_support())
                T[0,1]
                sage: T1 * T2
                T[1,2]
                sage: T2 * T1
                T[2,1]
                sage: T2 * (T2 * T1 * T0)
                -(1-q)*T[2,1,0] + q*T[1,0]
                sage: (T1 * T0 * T1 * T0) * T0
                (-u0*u1)*T[1,0,1] + ((u0+u1))*T[0,1,0,1]
                sage: (T0 * T1 * T0 * T1) * (T0 * T1)
                (-u0*u1*q)*T[1,0] + (u0*u1-u0*u1*q)*T[1,0,1]
                 + ((u0+u1)*q)*T[0,1,0] + ((-u0-u1)+(u0+u1)*q)*T[0,1,0,1]
                sage: T1 * (T0 * T2 * T1 * T0)
                T[1,0,2,1,0]
                sage: (T1 * T2) * (T2 * T1 * T0)
                -(1-q)*T[2,1,0,2] - (q-q^2)*T[1,0] + q^2*T[0]
                sage: (T2*T1*T2) * (T2*T1*T0*T1*T2)
                -(q-q^2)*T[2,1,0,1,2] + (1-2*q+q^2)*T[2,1,0,2,1,2]
                 - (q-q^2)*T[1,0,2,1,2] + q^2*T[0,2,1,2]

            We check some relations::

                sage: T0 * T1 * T0 * T1 == T1 * T0 * T1 * T0
                True
                sage: T1 * T2 * T1 == T2 * T1 * T2
                True
                sage: (T1 * T0) * T0 == T1 * (T0 * T0)
                True
                sage: (T.L(1) * T.L(2)) * T.L(2) - T.L(1) * (T.L(2) * T.L(2))
                0
                sage: (T.L(2) * T.L(3)) * T.L(3) - T.L(2) * (T.L(3) * T.L(3))
                0

            TESTS::

                sage: T = algebras.ArikiKoike(2, 3).T()
                sage: T0, T1, T2 = T.T()
                sage: (T1 * T0 * T1) * (T0 * T0)
                (-u0*u1)*T[1,0,1] + ((u0+u1))*T[0,1,0,1]
                sage: T1 * T.L(3) * T2 * T1 * T0 - T1 * (T.L(3) * T2 * T1 * T0)
                0

                sage: T = algebras.ArikiKoike(3, 3).T()
                sage: x = T.T(0) * T.T(1)
                sage: (x*x)*x == x*(x*x)
                True

                sage: T = algebras.ArikiKoike(3, 4).T()
                sage: L1 = T.L(1)
                sage: L2 = T.L(2)
                sage: (L2 * L1^2) * L2 == L2 * (L1^2 * L2)
                True
                sage: T1 = T.T(1)
                sage: (T1 * L1^2) * T1 * L1 * L1 == (T1 * L1^2) * T1 * L1^2
                True
            """
            # We represent T_i for i > 0 as S_i in comments to avoid confusion.
            # Product is of the form t1*s1 * t2*s2: separate the T's and permutations.
            t1, s1 = m1
            t2, s2 = m2
            one = self.base_ring().one()
            q = self._q
            qm1 = q - one

            # We first handle the case when s1 == 1
            if s1 == self._one_perm:
                if t1 == self._zero_tuple:
                    # Multiplying 1 * m2
                    return self._from_dict({m2: one}, remove_zeros=False)
                if t2 == self._zero_tuple:
                    return self._from_dict({(t1, s2): one}, remove_zeros=False)
                k1 = max(k for k,a in enumerate(t1) if a != 0)
                k2 = min(k for k,a in enumerate(t2) if a != 0)
                if k1 < k2:
                    T = list(t1)
                    for k in range(k2, len(t2)):
                        T[k] = t2[k]
                    return self._from_dict({(tuple(T), s2): one}, remove_zeros=False)
                # This is the most recursive part of the product
                M = self._product_TT(k1, t1[k1], k2, t2[k2])
                t1 = list(t1)
                t2 = list(t2)
                t1[k1] = 0
                t2[k2] = 0
                L = self._from_dict({(tuple(t1), self._one_perm): one}, remove_zeros=False)
                R = self._from_dict({(tuple(t2), s2): one}, remove_zeros=False)
                return L * M * R

            # The current product of T's and the type A Hecke algebra
            tprod = [( [(k, a) for k, a in enumerate(t2) if a != 0], {s2: one} )]

            # s1 through t2
            for i in reversed(s1.reduced_word()):
                new_t = []
                for index in range(len(tprod)):
                    j = i
                    T, sprod = tprod[index]
                    absorbed = False
                    for ind in range(len(T)):
                        k, a = T[ind]
                        # -1 from i since k is 0-based but i is 1-based
                        if j < k:
                            j += 1
                        elif j == k:
                            absorbed = True
                            # Quadratic relation: S_k^2 = (q - 1) S_k + q
                            # So S_{k-1} T_{k,a} = (q-1) T_{k,a} + q T_{k-1,a}
                            # Make a copy of T since we need to mutate it
                            new_t.append((list(T), {s: q * sprod[s] for s in sprod}))
                            new_t[-1][0][ind] = (k-1, a)
                            for s in sprod:
                                sprod[s] *= qm1
                            break
                        elif j == k + 1:
                            absorbed = True
                            T[ind] = (k+1, a)
                            break
                        # elif j > k: pass
                    if absorbed:
                        # We do not need to update tprod[index] because we
                        #   have mutated that pair of objects (T, sprod).
                        continue

                    # Do the usual Hecke product of S_j * S
                    temp = {} # start from 0
                    for p in sprod:
                        c = sprod[p]
                        # We have to flip the side due to Sage's
                        # convention for multiplying permutations
                        pj = p.apply_simple_reflection(j, side='left')
                        if p.has_descent(j, side='left'):
                            iaxpy(1, {p: c * qm1, pj: c * self._q}, temp)
                        else:
                            iaxpy(1, {pj: c}, temp)
                    tprod[index] = (T, temp)
                tprod.extend(new_t)

            # Compute t1 * T * sprod
            def compute(T, sprod):
                if not T:  # T=1, so just do t1 * sprod, each of which is in order
                    return self._from_dict({(t1, s): sprod[s] for s in sprod},
                                           remove_zeros=False, coerce=False)

                s_elt = self._from_dict({(self._zero_tuple, s): sprod[s] for s in sprod},
                                         remove_zeros=False, coerce=False)
                # Break T into basis vectors as much as possible to best take
                #   advantage of the caching
                cur = list(t1)
                product = [cur]
                if t1 != self._zero_tuple:
                    K = max(k for k, a in enumerate(t1) if a != 0)
                else:
                    K = -1
                T.reverse() # reverse the list so we can pop off the front
                while T:
                    k, a = T.pop()
                    if k > K:
                        cur[k] = a
                    else:
                        cur = list(self._zero_tuple)
                        cur[k] = a
                        product.append(cur)
                    K = k
                return self.prod(self._from_dict({(tuple(p), self._one_perm): one},
                                                 remove_zeros=False, coerce=False)
                                 for p in product) * s_elt

            return self.sum(compute(T, sprod) for T, sprod in tprod)

        @lazy_attribute
        def _T0_polynomial(self):
            r"""
            Return `p` such that `T0^{r-1} - p = \prod_{i=0}^{r-1} (T_0 - u_i)`.

            OUTPUT: a ``dict`` representing the polynomial `p`

            EXAMPLES::

                sage: T = algebras.ArikiKoike(4, 2).T()
                sage: T._T0_polynomial
                ((u0 + u1 + u2 + u3))*DUMMY^3
                 + ((-u0*u1 - u0*u2 - u1*u2 - u0*u3 - u1*u3 - u2*u3))*DUMMY^2
                 + ((u0*u1*u2 + u0*u1*u3 + u0*u2*u3 + u1*u2*u3))*DUMMY
                 - u0*u1*u2*u3
            """
            z = PolynomialRing(self.base_ring(), 'DUMMY').gen()
            # Remove the highest power
            return -prod(z - val for val in self._u).truncate(self._r)

        def _reduced_T0_power(self, exp):
            r"""
            Return the element `T_0` to the power ``exp`` in terms
            of `T_0^k` for `k < r`.

            EXAMPLES::

                sage: T = algebras.ArikiKoike(2, 3).T()
                sage: T._reduced_T0_power(1)
                1
                sage: T._reduced_T0_power(2)
                ((u0 + u1))*DUMMY - u0*u1
                sage: T._reduced_T0_power(3)
                ((u0^2 + u0*u1 + u1^2))*DUMMY + (-u0^2*u1 - u0*u1^2)
                sage: T._reduced_T0_power(4)
                ((u0^3 + u0^2*u1 + u0*u1^2 + u1^3))*DUMMY
                 + (-u0^3*u1 - u0^2*u1^2 - u0*u1^3)
                sage: T._reduced_T0_power(5)
                ((u0^4 + u0^3*u1 + u0^2*u1^2 + u0*u1^3 + u1^4))*DUMMY
                 + (-u0^4*u1 - u0^3*u1^2 - u0^2*u1^3 - u0*u1^4)
            """
            if exp < self._r:
                return self.base_ring().one()
            PR = self._T0_polynomial.parent()
            z = PR.gen()
            cur = z ** exp
            while cur.degree() >= self._r:
                cur = (PR.sum(coeff * self._T0_polynomial * z**e
                             for e, coeff in enumerate(cur.list()[self._r:]))
                       + cur.truncate(self._r))
            return cur

        @cached_method
        def _product_TT(self, kp, a, k, b):
            r"""
            Return the product `T_{k',a} T_{k,b}` with `k' \geq k` in terms
            of the basis elements of ``self``.

            From Lemma 2.3 of [BM1997]_, we have

            .. MATH::

                T_{k',a} T_{k,b} = T_{k-1,b} T_{k',a} T_1
                  + (q - 1) \sum_{i=1}^b T_{k-1,a+b-i} T_{k',i}
                                         - T_{k-1,i} T_{k',a+b-i}.

            INPUT:

            - ``kp``, ``k`` -- 0-based indices
            - ``a``, ``b`` -- the exponents of the `T_0` generator

            EXAMPLES::

                sage: T = algebras.ArikiKoike(4, 3).T()
                sage: T._product_TT(1, 0, 0, 1)
                T[1,0]
                sage: T._product_TT(1, 1, 0, 1)
                T[1,0,0]
                sage: T._product_TT(1, 2, 0, 1)
                T[1,0,0,0]
                sage: T._product_TT(1, 3, 0, 1)
                (-u0*u1*u2*u3)*T[1]
                 + ((u0*u1*u2+u0*u1*u3+u0*u2*u3+u1*u2*u3))*T[1,0]
                 + ((-u0*u1-u0*u2-u1*u2-u0*u3-u1*u3-u2*u3))*T[1,0,0]
                 + ((u0+u1+u2+u3))*T[1,0,0,0]
                sage: T._product_TT(1, 2, 0, 2)
                (-u0*u1*u2*u3)*T[1]
                 + ((u0*u1*u2+u0*u1*u3+u0*u2*u3+u1*u2*u3))*T[1,0]
                 + ((-u0*u1-u0*u2-u1*u2-u0*u3-u1*u3-u2*u3))*T[1,0,0]
                 + ((u0+u1+u2+u3))*T[1,0,0,0]
                sage: T._product_TT(2, 1, 0, 3)
                (-u0*u1*u2*u3)*T[2,1]
                 + ((u0*u1*u2+u0*u1*u3+u0*u2*u3+u1*u2*u3))*T[2,1,0]
                 + ((-u0*u1-u0*u2-u1*u2-u0*u3-u1*u3-u2*u3))*T[2,1,0,0]
                 + ((u0+u1+u2+u3))*T[2,1,0,0,0]

            TESTS::

                sage: H = algebras.ArikiKoike(3, 4)
                sage: T = H.T()
                sage: T._product_TT(1, 2, 1, 2)
                (-u0*u1*u2+u0*u1*u2*q)*T[1,0]
                 + (u0*u1*u2-u0*u1*u2*q)*T[0,1]
                 + ((u0+u1+u2)+(-u0-u1-u2)*q)*T[0,1,0,0]
                 + ((-u0-u1-u2)+(u0+u1+u2)*q)*T[0,0,1,0]
                 + T[0,0,1,0,0,1]
                sage: T._product_TT(2,2,2,2)
                (-u0*u1*u2+u0*u1*u2*q)*T[2,1,0,2]
                 + (u0*u1*u2-u0*u1*u2*q)*T[1,0,2,1]
                 + ((u0+u1+u2)+(-u0-u1-u2)*q)*T[1,0,2,1,0,0]
                 + ((-u0-u1-u2)+(u0+u1+u2)*q)*T[1,0,0,2,1,0]
                 + T[1,0,0,2,1,0,0,1]
                sage: T._product_TT(3,2,3,2)
                (-u0*u1*u2+u0*u1*u2*q)*T[3,2,1,0,3,2]
                 + (u0*u1*u2-u0*u1*u2*q)*T[2,1,0,3,2,1]
                 + ((u0+u1+u2)+(-u0-u1-u2)*q)*T[2,1,0,3,2,1,0,0]
                 + ((-u0-u1-u2)+(u0+u1+u2)*q)*T[2,1,0,0,3,2,1,0]
                 + T[2,1,0,0,3,2,1,0,0,1]
            """
            # Quadratic relation: S_i^2 - (q - 1) S_i - q == 0
            # [BM1997]_: S_i^2 - (q_1 + q_2) S_i + q_1 q_2 == 0
            # Implies q_1 = q, q_2 = -1
            one = self.base_ring().one()
            # Case T_{k',a} T_0^b = T_{k',a+b}
            if k == 0:
                if a + b < self._r:
                    T = list(self._zero_tuple)
                    T[kp] = a + b
                    return self._from_dict({(tuple(T), self._one_perm): one},
                                           remove_zeros=False, coerce=False)

                def key(exp):
                    if exp > 0 or kp == 0:
                        T = list(self._zero_tuple)
                        T[kp] = exp
                        return (tuple(T), self._one_perm)
                    # Note that kp is 0-based, but our 0-index in the T portion
                    #   is the power of T_0
                    perm = self._Pn.one()
                    for j in range(1, kp+1):
                        perm = perm.apply_simple_reflection_left(j)
                    return (self._zero_tuple, perm)
                p = self._reduced_T0_power(a + b)
                zero = self.base_ring().zero()
                return self._from_dict({key(exp): coeff
                                        for exp, coeff in enumerate(p)
                                        if coeff != zero},
                                       remove_zeros=False, coerce=False)

            # Otherwise k > 0
            assert kp >= k
            s1 = self._Pn.simple_reflection(1)
            qm1 = self._q - one
            T = list(self._zero_tuple)
            T[k-1] = b
            T[kp] = a
            ret = {(tuple(T), s1): one}
            zero = self.base_ring().zero()

            def T_index(exp, ind, i, indp):
                T = list(self._zero_tuple)
                T[ind] = exp
                T[indp] = i
                return tuple(T)
            for i in range(1, b+1):
                if a + b - i == i:
                    continue
                if a + b - i < self._r:
                    T[k-1] = a + b - i
                    T[kp] = i
                    m = (tuple(T), self._one_perm)
                    T[k-1] = i
                    T[kp] = a + b - i
                    mp = (tuple(T), self._one_perm)
                    iaxpy(1, {m: qm1, mp: -qm1}, ret)
                else:
                    p = self._reduced_T0_power(a + b - i)
                    temp = {(T_index(exp, k-1, i, kp), self._one_perm): qm1 * coeff
                            for exp, coeff in enumerate(p) if coeff != zero}
                    if p[0] != zero and k > 1:
                        # We need to add back in the permutation for the "T_{k-1,0}"
                        #    in the reduction from T_{k-1,a+b-i}
                        perm = self._Pn.one()
                        for j in range(2, k+1):  # Recall k is 0-based, we add 1 back from Lemma 2.3(a)
                            perm = perm.apply_simple_reflection_left(j)
                        tind = T_index(0, k-1, i, kp)
                        temp[(tind, perm)] = temp[(tind, self._one_perm)]
                        del temp[(tind, self._one_perm)]
                    iaxpy(1, temp, ret)
                    temp = {(T_index(exp, kp, i, k-1), self._one_perm): -qm1 * coeff
                            for exp, coeff in enumerate(p) if coeff != zero}
                    if p[0] != zero:
                        # We need to add back in the permutation for the "T_{k',0}"
                        #    in the reduction from T_{k',a+b-i}
                        perm = self._Pn.one()
                        for j in range(1, kp+1):  # Recall kp is 0-based
                            perm = perm.apply_simple_reflection_left(j)
                        tind = T_index(0, kp, i, k-1)
                        temp[(tind, perm)] = temp[(tind, self._one_perm)]
                        del temp[(tind, self._one_perm)]
                    iaxpy(1, temp, ret)

            return self._from_dict(ret, remove_zeros=False)

        def cellular_involution(self, m):
            """
            Return the cellular involution of the basis element indexed by
            ``m`` in ``self``.
            """
            for i, k in enumerate(m[0]):
                if not k:
                    continue
                redword += list(reversed(range(1,i+1))) + [0]*k
            redword += m[1].reduced_word()
            T = self.T()
            return self.prod(T[i] for i in reversed(redword))

    # -----------------------------------------------------
    # Cellular basis classes
    # -----------------------------------------------------

    class Murphy(_CellularBasis):
        """
        The Murphy basis of the Ariki-Koike algebra.
        """
        _prefix = 'M'

        @cached_method
        def one_basis(self):
            r"""
            Return the index of the basis element of `1`.

            EXAMPLES::

                sage: M = algebras.ArikiKoike(2, 3).Murphy()
                sage: M.one_basis()
                ((0, 0, 0), [1, 2, 3])
            """
            la = PartitionTuples()([[]]*(self._r-1) + [[self._r]])
            return (la, StandardTableauTuples(la)[0], StandardTableauTuples(la)[0])

        @cached_method
        def _m_elt(self, la):
            r"""
            Return the element `m_{\lambda}` in ``self``.
            """
            LT = self.realization_of().LT()
            Pn = LT._Pn
            zt = LT._zero_tuple
            xla = LT.sum_of_monomials((zt, Pn(w.tuple())) for w in la.young_subgroup())
            u = LT._u
            L = LT.L()
            uplus = LT.prod(L[k] - u[s] for s in range(1, LT._r)
                            for k in range(sum(sum(part) for part in la[:s])))
            return xla * uplus

        @cached_method
        def _to_LT(self, m):
            r"""
            Return the basis element indexed by ``m`` in ``self``
            in the TL basis.
            """
            la, s, t = m
            LT = self.realization_of().LT()
            T = LT.T()
            Pn = LT._Pn
            ds = Pn(list(sum((row for tab in s for row in tab), ())))
            dt = Pn(list(sum((row for tab in t for row in tab), ())))
            return (LT.monomial((LT._zero_tuple, ds))
                    * self._m_elt(la)
                    * LT.prod(T[i] for i in reversed(dt.reduced_word())))

        @cached_method
        def L(self, i=None):
            r"""
            Return the Jucys-Murphy element(s) `L_i`.
            """
            if i is None:
                return tuple([self.L(j) for j in range(1, self._n+1)])
            return self(self._algebra.L(i))

    class Seminormal(_CellularBasis):
        """
        The seminormal basis of the Ariki-Koike algebra.
        """
        _prefix = 'S'

        @cached_method
        def one(self):
            r"""
            Return the element of `1`.

            EXAMPLES::

                sage: S = algebras.ArikiKoike(2, 3).Seminormal()
                sage: S.one()
                S[-|1/2/3, -|1/2/3] + S[-|1,2/3, -|1,2/3] + S[-|1,3/2, -|1,3/2]
                 + S[-|1,2,3, -|1,2,3] + S[1|2/3, 1|2/3] + S[2|1/3, 2|1/3]
                 + S[3|1/2, 3|1/2] + S[1|2,3, 1|2,3] + S[2|1,3, 2|1,3]
                 + S[3|1,2, 3|1,2] + S[1/2|3, 1/2|3] + S[1/3|2, 1/3|2]
                 + S[2/3|1, 2/3|1] + S[1/2/3|-, 1/2/3|-] + S[1,2|3, 1,2|3]
                 + S[1,3|2, 1,3|2] + S[2,3|1, 2,3|1] + S[1,2/3|-, 1,2/3|-]
                 + S[1,3/2|-, 1,3/2|-] + S[1,2,3|-, 1,2,3|-]
            """
            one = self.base_ring().one()
            return self.element_class(self, {(la, t, t): one
                                             for la in PartitionTuples(self._r, self._n)
                                             for t in StandardTableauTuples(la)})

        @cached_method
        def L(self, i=None):
            r"""
            Return the Jucys-Murphy element(s) `L_i`.

            By Corollary 2.18 in [Mathas2002]_, the Jucys-Murphy element
            `L_i` is equal to

            .. MATH::

                L_i = \sum_t \mathrm{res}_t(i) F_t,

            where `F_t` is the :meth:`primitive_idempotent` and
            `\mathrm{res}_t(i) = q^{c-r} u_s` is the *residue* of `i`
            in `t` (which occurs in row `r` and column `c` of the `s`-th
            tableau of `t`).

            INPUT:

            - ``i`` -- (default: ``None``) the Jucys-Murphy element `L_i`
              or if ``None``, then the list of all `L_i`

            EXAMPLES::

                sage: S = algebras.ArikiKoike(2, 3).Seminormal()
                sage: S.L(2)
                (q^-1)*T[1,0,1]
                sage: S.L()
                [T[0], (q^-1)*T[1,0,1], (q^-2)*T[2,1,0,1,2]]

                sage: S = algebras.ArikiKoike(8, 3).Seminormal()
                sage: T0,T1,T2 = S.T()
                sage: q = T.q()
                sage: S.L(1) == T0
                True
                sage: S.L(2) == q^-1 * T1*T0*T1
                True
                sage: S.L(3) == q^-2 * T2*T1*T0*T1*T2
                True

                sage: S = algebras.ArikiKoike(1, 3).Seminormal()
                sage: S.L(2)
                (u*q^-1)*S[1/2/3, 1/2/3] + u*q*S[1,2/3, 1,2/3]
                 + (u*q^-1)*S[1,3/2, 1,3/2] + u*q*S[1,2,3, 1,2,3]
                sage: S.L()
                [u,
                 u + (-u*q^-1+u)*T[1],
                 u + (-u*q^-1+u)*T[2] + (-u*q^-2+u*q^-1)*T[2,1,2]]

            TESTS:

            Check that the Jucys-Murphy elements form a commutative
            subring::

                sage: S = algebras.ArikiKoike(8, 4).Seminormal()
                sage: L = S.L()
                sage: all(x*y == y*x for x in L for y in L)
                True

                sage: S = algebras.ArikiKoike(2, 3).Seminormal()
                sage: L = S.L()
                sage: all(x*y == y*x for x in L for y in L)
                True

                sage: S = algebras.ArikiKoike(1, 4).Seminormal()
                sage: L = S.L()
                sage: all(x*y == y*x for x in L for y in L)
                True
            """
            if i is None:
                return tuple([self.L(j) for j in range(1, self._n+1)])
            return self._from_dict({(la, t, t): self._res(t, i)
                                    for la in PartitionTuples(self._r, self._n)
                                    for t in StandardTableauTuples(la)})

        @cached_method
        def T(self, i=None):
            r"""
            Return the generator(s) `T_i` of ``self``.

            INPUT:

            - ``i`` -- (default: ``None``) the generator `T_i` or
              if ``None``, then the list of all generators `T_i`
            """
            if i is None:
                return [self.T(j) for j in range(self._n)]
            if i == 0:
                return self.L(1)
            # Compute the action 1 * T(i)
            return self.sum(self._T_action_on_basis(i, (la, t, t))
                            for la in PartitionTuples(self._r, self._n)
                            for t in StandardTableauTuples(la))

        def primitive_idempotent(self, t):
            r"""
            Return the primitive idempotent `F_t` in ``self``.

            These are precisely the basis elements `S_{tt}` of ``self``.

            EXAMPLES::

                sage: S = algebras.ArikiKoike(8, 4).Seminormal()
                sage: B = S.basis()
                sage: STT = B.keys()[1]
            """
            t = StandardTableauTuples(self._r, self._n)(t)
            la = t.shape()
            t = self.cell_module_indices(la)(t)
            return self.basis()[la, t, t]

        def _res(self, t, i):
            """
            Return the residue of ``i`` in ``t`` in ``self``.
            """
            if t.level() == 1:
                t = [t]
            for l, tableau in enumerate(t):
                for r, row in enumerate(tableau):
                    try:
                        return self._q**(row.index(i) - r) * self._u[l]
                    except ValueError:
                        pass
            assert False, f"BUG: no residue for {i} in {t}"

        @cached_method
        def gamma(self, t):
            Pn = self._algebra._Pn
            val_cells = {val: (l, r, c) for l, tableau in enumerate(t)
                         for r, row in enumerate(tableau)
                         for c, val in enumerate(row)}

            la = t.shape()
            alpha = sum((val-1) * val for lak in la for val in lak) / ZZ(2)
            dt = Pn(list(sum((row for tab in t for row in tab), ())))

            return q ** (dt.length() + alpha) * ret

        @cached_method
        def _from_LT(self, m):
            Lprod = self.prod(self.L(i)**val for val in m[0])
            Tprod = self.prod(self.T(i) for val in m[1].reduced_word())
            return Lprod * Tprod

        @cached_method
        def _to_LT(self, m):
            pass

        def _T_action_on_basis(self, i, m):
            if i == 0:
                return self._L_on_basis(1, m)
            la, v, t = m
            R = self.base_ring()

            ct = t.cells_containing(i)[0]
            cs = t.cells_containing(i+1)[0]
            if len(ct) == 2: # it is of level 1 and a regular tableau
                ct = (0,) + ct
                cs = (0,) + cs

            if ct[0] == cs[0] and ct[2] == cs[2]: # same column
                return self.element_class(self, {(la, v, t): -R.one()})

            if ct[0] == cs[0] and ct[1] == cs[1]: # same row
                return self.element_class(self, {(la, v, t): self._q})

            # result is standard
            s = t.symmetric_group_action_on_entries(self._Pn.simple_reflection(i))
            assert s.parent() is t.parent()

            def res(cell):
                return self._q**(cell[2] - cell[1]) * self._u[cell[0]]

            # Note that the residue of i in t is given by the cell c
            #   and of i in s corresponds to cell cp because the
            #   corresponding action of the permutation on t.
            one = self.base_ring().one()
            denom = res(cs) - res(ct)
            coefft = (self._q - one) * res(cs) / denom
            coeffs = (self._q * res(ct) - res(cs)) / denom
            return self.element_class(self, {(la, v, t): R(coefft), (la, v, s): R(coeffs)})

        def _L_action_on_basis(self, i, m):
            return self.term(m, self._res(m[2], i))

        @cached_method
        def product_on_basis(self, m1, m2):
            if m1[2] != m2[1]:
                return self.zero()
            return self.term((m1[0], m1[1], m2[2]), self.gamma(m1[2]))
