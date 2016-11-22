"""
Khovanov-Lauda-Rouquier (KLR) Algebras

AUTHORS:

- Travis Scrimshaw, Mee Seong Im (2016-11): initial version
"""

#*****************************************************************************
#  Copyright (C) 2016 Travis Scrimshaw <tscrimsh at umn.edu>
#                2016 Mee Seong Im <meeseongim at gmail.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  http://www.gnu.org/licenses/
#*****************************************************************************

from sage.misc.cachefunc import cached_method
from sage.categories.algebras import Algebras
from sage.categories.cartesian_product import cartesian_product
from sage.combinat.free_module import CombinatorialFreeModule
from sage.combinat.permutation import Permutations
from sage.sets.family import Family
from sage.sets.finite_enumerated_set import FiniteEnumeratedSet
from sage.monoids.free_abelian_monoid import FreeAbelianMonoid

class KLRAlgebra(CombinatorialFreeModule):
    r"""
    A Khovanov-Lauda-Rouquier (KLR) algebra.

    A *Khovanov-Lauda-Rouquier (KLR) algebra*, also sometimes known as
    a *quiver Hecke algebra* is a diagramatic algebra that satisfies
    certain relations. They can be considered as a categorification
    of the crystal `B(\infty)` and their cyclotomic quotients
    categorify highest weight crystals.

    INPUT:

    - ``R`` -- the base ring
    - ``cartan_type`` -- the Cartan type (of rank `n`)
    - ``wt`` -- the weight given as `n`-tuple
    """
    @staticmethod
    def __classcall_private__(cls, R, cartan_type, wt, prefix='KLR'):
        """
        Normalize input.
        """
        return super(KLRAlgebra, cls).__classcall__(cls, R, CartanMatrix(cartan_type),
                                                    tuple(wt), prefix)

    def __init__(self, R, cartan_matrix, wt, prefix):
        """
        Initialize ``self``.
        """
        self._cartan_matrix = cartan_matrix
        self._weight = wt
        self._d = sum(wt)

        # Reduced words
        #red_words = Family(Permutations(self._d), lambda p: tuple(p.reduced_word()))
        red_words = FiniteEnumeratedSet([tuple(p.reduced_word())
                                         for p in Permutations(self._d)])
        red_words.rename("reduced words of S_{}".format(self._d))
        # The monomials
        M = FreeAbelianMonoid(self._d, names=['x%s'%i for i in range(1, self._d+1)])
        # Idempotents (i.e. the colors of the strands)
        index_set = self._cartan_matrix.index_set()
        P = Permutations(sum([[index_set[i]]*v for i,v in enumerate(wt)],[]))
        I = cartesian_product([red_words, M, P])
        CombinatorialFreeModule.__init__(self, R, I, prefix=prefix,
                                         monomial_key=KLRAlgebra._monomial_key,
                                         category=Algebras(R).WithBasis().Graded())

    @staticmethod
    def _monomial_key(a):
        """
        The key for comparing the monomial indexed by ``a``.
        """
        return (a[0], a[1]._element_vector, a[2])

    def _repr_(self):
        """
        Return a string representation of ``self``.
        """
        return "KLR Algebra of type {} and weight {} over {}".format(self._cartan_matrix.cartan_type(), self._weight, self.base_ring())

    def _repr_term(self, m):
        r"""
        Return a string representation of the term indexed by ``m``.
        """
        cur = self.prefix() + '['
        if m[0]:
            cur += '*'.join('s{}'.format(i) for i in m[0])
        if sum(m[1].list()) == 0:
            if not m[0]:
                cur += '1'
            cur += '*'
        else:
            for i,v in enumerate(m[1].list()):
                if v == 1:
                    cur += 'x{}*'.format(i+1,v)
                elif v > 1:
                    cur += 'x{}^{}*'.format(i+1,v)
        cur += repr(m[2]) + ']'
        return cur

    def _latex_term(self, m):
        r"""
        Return a latex representation of the term indexed by ``m``.
        """
        cur = ''
        if m[0]:
            cur += ' '.join('s_{{{}}}'.format(i) for i in m[0])
        for i,v in enumerate(m[1].list()):
            if v == 1:
                cur += ' x_{}'.format(i+1)
            elif v > 1:
                cur += ' x_{}^{}'.format(i+1,v)
        cur += ' \mathbf{{1}}_{{{}}}'.format(m[2])
        return cur

    @cached_method
    def algebra_generators(self):
        """
        Return the algebra generators of ``self``.
        """
        M = self._indices._sets[1] # The monomials
        wt = M.one() # The identity of the monomials
        P = self._indices._sets[2] # The idemponents

        I = ['s%i'%i for i in range(1, self._d)]  # The transpositions
        I += ['x%i'%i for i in range(1, self._d+1)] # The beads
        I += list(tuple(x) for x in P) # For the idempotents
        d = {}
        for i in range(1,self._d):
            d['s%i'%i] = self.sum_of_monomials( ((i,), wt, x) for x in P )
            d['x%i'%i] = self.sum_of_monomials( ((), M.gen(i-1), x) for x in P )
        d['x%i'%self._d] = self.sum_of_monomials( ((), M.gen(self._d-1), x) for x in P )
        for x in P:
            d[tuple(x)] = self.monomial( ((), wt, x) )
        return Family(I, lambda x: d[x], name="generator map")

    @cached_method
    def one(self):
        """
        Return the identity element `1` in ``self``.
        """
        wt = self._indices._sets[1].one() # The identity of the monomials
        I = self._indices._sets[2] # the ordered set partitions
        return self.sum_of_monomials( ((), wt, la) for la in I )

    def degree_on_basis(self, m):
        """
        The degree of the basis element of ``self`` labelled by ``m``, i.e.,
        the degree of the triple (reduced expression, m, perm).

        INPUT:

        - ``m`` -- an element of the free abelian monoid

        OUTPUT: an integer, the degree of the corresponding basis element
        """
        cm = self._cartan_matrix
        sym = cm.symmetrized_matrix()
        # The s_i contributions
        deg = sum(sym[m[2][j-1]-1, m[2][j]-1] for j in m[0])
        # The x_i contributions
        deg += sum(sym[m[2][i]-1, m[2][i]-1] * v for i,v in enumerate(m[1]._element_vector))
        return deg

    # Everything above this line is working.

    def product_on_basis(self, L, R):
        """
        Return the product of two basis elements indexed by ``L`` and ``R``.
        """
        # Assume braid, beads, idempotent order
        sl, xl, Il = L
        sr, xr, Ir = R
        M = self._indices._sets[1] # The monomials
        P = self._indices._sets[2] # The idemponents

        print(L)
        print(R)
        print("")

        # Nothing to permute, so we check idempotents and multiply beads
        if not sr:
            if Il != Ir:  # Idempotent mismatch
                return self.zero()
            return self.monomial((sl, xl * xr, Il))

        # Non-trivial permutation, work to do:
        # 1 - Check idempotents (quick)
        # 2 - Move xl past sr (slide beads top to bottom)
        # 3 - Braid moves (hard)

        # Step 1: Idempotents
        # ------
        lst = list(Il)
        for i in sr:
            lst[i-1], lst[i] = lst[i], lst[i-1]
        if lst != list(Ir):  # Idempotent mismatch
            return self.zero()

        # Step 2: beads -> perm
        # ------
        i = sr[0]
        x = xl.list()
        if x[i-1] != 0 or x[i] != 0:
            if Il[i-1] != Il[i]: # Different colors
                lst = list(Il)
                lst[i-1], lst[i] = lst[i], lst[i-1]
                x[i-1], x[i] = x[i], x[i-1]
                return ( self.monomial((sl, M.one(), Il))
                         * self.monomial(((i,), M(x), P(lst)))
                         * self.monomial((sr[1:], xr, Ir)) )

            # Otherwise same color
            def M_elt(x, a, b):
                """
                Construct `x_{i-1}^a x_i^b` (0-based `i`) with the rest of
                the beads from ``x``.
                """
                ret = list(x)
                ret[i-1] = a
                ret[i] = b
                return M(ret)

            lst = list(Il)
            lst[i-1], lst[i] = lst[i], lst[i-1]
            x[i-1], x[i] = x[i], x[i-1]
            one = self.base_ring().one()
            # x_i^k x_{i+1}^l s_i = s_i x_i^l x_{i+1}^k
            #                       + \sum_{a=0}^{k-1} x_i^{a+l} x_{i+1}^{k-1-a}
            #                       - \sum_{a=0}^{l-1} x_i^{a+k} x_{i+1}^{l-1-a}
            # k = x[i], l = x[i-1]
            mid = self.monomial(((i,), M(x), P(lst)))
            mid += self._from_dict({((), M_elt(x, a+x[i-1], x[i]-1-a), P.one()): one
                                    for a in range(x[i])},
                                   coerce=False, remove_zeros=False)
            mid += self._from_dict({((), M_elt(x, a+x[i], x[i-1]-1-a), P.one()): one
                                    for a in range(x[i-1])},
                                   coerce=False, remove_zeros=False)
            return ( self.monomial((sl, M.one(), Il))
                     * mid
                     * self.monomial((sr[1:], xr, Ir)) )

        # Step 3: perm * perm
        # ------
        raise NotImplementedError


