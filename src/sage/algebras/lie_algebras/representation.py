r"""
Representations of Lie Algebras

EXAMPLES::

    sage: La = RootSystem(['E',6]).weight_lattice().fundamental_weights()
    sage: M = crystals.NakajimaMonomials(La[1])
    sage: VM = ReprMinuscule(M, QQ)
    sage: v = VM.maximal_vector()
    sage: x = (tensor([v, v.f(1), v.f(1).f(3)])
    ....:      - tensor([v.f(1), v, v.f(1).f(3)])
    ....:      - tensor([v, v.f(1).f(3), v.f(1)])
    ....:      + tensor([v.f(1), v.f(1).f(3), v])
    ....:      + tensor([v.f(1).f(3), v, v.f(1)])
    ....:      - tensor([v.f(1).f(3), v.f(1), v])
    ....:      )
    sage: all(x.e(i) == 0 for i in M.index_set())
    True
    sage: S = SubRepresentation(x, crystals.NakajimaMonomials(La[4]))
       initializing _build_basis
       building basis
       running checks
    sage: verify_representation(S)  # long time -- multiple minutes

    sage: B4 = S.basis().keys()
    sage: wt0 = [b for b in B4 if b.weight() == 0]
    sage: S0 = [S.basis()[b] for b in wt0]
    sage: def build_smat(i):
    ....:     ret = []
    ....:     for b in S0:
    ....:         bs = b.s(i)
    ....:         ret.append([bs[c] for c in wt0])
    ....:     return matrix(ret)
    sage: s_mats = [build_smat(i) for i in B4.index_set()]

    sage: [m.det() for m in s_mats]
    [-1, -1, -1, -1, -1, -1]
    sage: W = WeylGroup(['E',6], prefix='s')
    sage: W.cardinality()
    51840
    sage: MG = MatrixGroup(s_mats)
    sage: MG.cardinality()   # long time - few minutes computation
    51840
"""

#from sage.combinat.dict_addition import dict_addition, dict_linear_combination
from sage.categories.category_types import Category_module
from sage.categories.modules import Modules
from sage.categories.category_with_axiom import CategoryWithAxiom_over_base_ring
from sage.combinat.free_module import (CombinatorialFreeModule,
                                       CombinatorialFreeModule_Tensor,
                                       CombinatorialFreeModule_CartesianProduct)
from sage.algebras.lie_algebras.poincare_birkhoff_witt import PoincareBirkhoffWittBasis
from sage.misc.lazy_attribute import lazy_attribute


# -------------------------------------------------------------------
# Categories of Lie algebra representations

class LieAlgebraRepresentations(Category_module):
    """
    Category of Lie algebra representations.
    """
    def __init__(self, g):
        self._g = g
        R = g.base_ring()
        super().__init__(R)

    class CartesianProducts(CartesianProductsCategory):
        r"""
        The category Lie algebra representations constructed as Cartesian
        products of Lie algebra representations.

        This is the direct sum of the Lie algebra representations.
        """
        @cached_method
        def extra_super_categories(self):
            return [self.base_category()]

    class TensorProducts(TensorProductsCategory):
        """
        The category of Lie algebra representations constructed by
        tensor product of Lie algebra representations.
        """
        @cached_method
        def extra_super_categories(self):
            return [self.base_category()]


class KacMoodyRepresentations(Category_module):
    """
    Category of Kac-Moody Lie algebra representations.
    """
    def super_categories(self):
        return [LieAlgebraRepresentations(self.base_ring())]

    class ParentMethods:
        def _test_kac_moody_relations(self, **options):
            tester = self._tester(**options)
            ct = self.cartan_type()
            d = ct.symmetrizer()
            I = ct.index_set()
            A = ct.cartan_matrix()
            al = RootSystem(ct).weight_lattice().simple_roots()
            ac = RootSystem(ct).weight_lattice().simple_coroots()

            from sage.misc.misc import some_tuples
            from sage.categories.sets_cat import cartesian_product
            LX = self._g.some_elements()
            C = cartesian_product([I, I, tester.some_elements()])
            for i, j, x in some_tuples(C, None, tester._max_runs):
                tester.assertEqual(x.e(j).h(i,1) - x.h(i,1).e(j), al[i].scalar(ac[j]) * x.e(j),
                                   "[h,e] = Ae -- i: {}, j: {}, x: {}".format(i, j, x))
                tester.assertEqual(x.f(j).h(i,1) - x.h(i,1).f(j), -al[i].scalar(ac[j]) * x.f(j),
                                   "[h,f] = -Af -- i: {}, j: {}, x: {}".format(i, j, x))
                if i == j:
                    tester.assertEqual(x.f(i).e(i) - x.e(i).f(i), x.h(i,1),
                                       "[e,f] = h -- i: {} == j: {}".format(i, j))
                    continue
                tester.assertEqual(x.f(j).e(i) - x.e(i).f(j), 0, "[e,f] = 0 -- i: {} j: {}".format(i, j))
                # Check Serre
                aij = A[I.index(i), I.index(j)]
                tester.assertEqual(sum((-1)^n
                                       * binomial(1-aij, n)
                                       * apply_e([i]*(1-aij-n) + [j] + [i]*n, x)
                                       for n in range(1-aij+1)),
                                   0,
                                   "Serre e -- i: {}, j: {}".format(i, j))
                tester.assertEqual(sum((-1)^n
                                       * binomial(1-aij, n)
                                       * apply_f([i]*(1-aij-n) + [j] + [i]*n, x)
                                       for n in range(1-aij+1)),
                                   0,
                                   "Serre f -- i: {}, j: {}".format(i, j))

        def cartan_type(self):
            return self._g.cartan_type()

    class WithBasis(CategoryWithAxiom_over_base_ring):
        class ElementMethods:
            def e(self, i):
                F = self.parent()
                return F.linear_combination((F.e_on_basis(i, m), c)
                                             for m,c in self.monomial_coefficients(copy=False).items())

            def f(self, i):
                F = self.parent()
                return F.linear_combination((F.f_on_basis(i, m), c)
                                             for m,c in self.monomial_coefficients(copy=False).items())

            def h(self, i, power=1):
                """
                Return the action of `h_i` on ``self``.

                We assume everything is working in a weight basis, so we have
                :meth:`h_on_basis()` return the appropriate scalar.
                """
                F = self.parent()
                return F._from_dict({m: c * F.h_on_basis(i, m, power)
                                     for m, c in self.monomial_coefficients(copy=False).items()})

            def s(self, i):
                """
                Return the action of `s_i` on ``self``.
                """
                fop = lambda x: x.f(i)
                eop = lambda x: -x.e(i)
                return self.exp(fop).exp(eop).exp(fop)

    class WithBasis(CategoryWithAxiom_over_base_ring):
        class TensorProducts(TensorProductsCategory):
            class ParentMethods:
                def e_on_basis(self, i, b):
                    mon = [self._sets[k].monomial(elt) for k,elt in enumerate(b)]
                    t = self.tensor_constructor(self._sets)
                    ret = self.zero()
                    for k,elt in enumerate(b):
                        ret += t(*(mon[:k] + [self._sets[k].e_on_basis(i, elt)] + mon[k+1:]))
                    return ret

                def f_on_basis(self, i, b):
                    mon = [self._sets[k].monomial(elt) for k,elt in enumerate(b)]
                    t = self.tensor_constructor(self._sets)
                    ret = self.zero()
                    for k,elt in enumerate(b):
                        ret += t(*(mon[:k] + [self._sets[k].f_on_basis(i, elt)] + mon[k+1:]))
                    return ret

                def h_on_basis(self, i, b, power=1):
                    return sum(self._sets[k].h_on_basis(i, elt, power) for k,elt in enumerate(b))

        class CartesianProducts(CartesianProductsCategory):
            class ParentMethods:
                def e_on_basis(self, i, b):
                    ind, key = b
                    return self.cartesian_embedding(self._sets[ind].e_on_basis(i, key))

                def f_on_basis(self, i, b):
                    ind, key = b
                    return self.cartesian_embedding(self._sets[ind].f_on_basis(i, key))

                def h_on_basis(self, i, b, power=1):
                    ind, key = b
                    return self.cartesian_embedding(self._sets[ind].h_on_basis(i, key, power))


class HighestWeightRepresentations(Category_module):
    """
    Category of highest weight Lie algebra representations.
    """
    def super_categories(self):
        return [LieAlgebraRepresentations(self.base_ring()).Graded()]

    class ParentMethods:
        @abstract_method
        def maximal_vector(self):
            r"""
            Return the maximal vector of ``self``.
            """

        def highest_weight(self):
            r"""
            Return the highest weight of ``self``.
            """
            return self.maximal_vector().degree()


class CategoryO(Category_module):
    def __init__(self, g):
        self._g = g
        super().__init__(R)

    def super_categories(self):
        return [KacMoodyRepresentations(self._g).Graded()]

    class CartesianProducts(CartesianProductsCategory):
        r"""
        The category `\mathcal{O}` constructed as Cartesian products of
        modules in `\mathcal{O}`.

        This is the direct sum of the Kac-Moody representations.
        """
        @cached_method
        def extra_super_categories(self):
            return [self.base_category()]

    #class WithBasis(CategoryWithAxiom_over_base_ring):
    #    pass

    # NOTE: Not closed under tensor products

    class FiniteDimensional(CategoryWithAxiom_over_base_ring):
        class TensorProducts(TensorProductsCategory):
            r"""
            The finite dimensional category `\mathcal{O}` representations
            constructed by a tensor product of Lie algebra finite dimensional
            category `\mathcal{O}`.
            """
            @cached_method
            def extra_super_categories(self):
                return [self.base_category()]


# -------------------------------------------------------------------

class Representation(CombinatorialFreeModule):
    r"""
    A representation of a Lie algebra (with a fixed basis).
    """
    def __init__(self, g, indices, **kwds):
        r"""
        Initialize ``self``.
        """
        self._g = g
        R = g.base_ring()
        category = LieAlgebraRepresentations(g).WithBasis().or_subcategory(kwds.pop("category", None))
        super().__init__(self, R, indices=indices, category=category, **kwds)

    def _test_reprsentation(self, **options):
        tester = self._tester(**options)
        from sage.misc.misc import some_tuples
        from sage.categories.sets_cat import cartesian_product
        LX = self._g.some_elements()
        C = cartesian_product([LX, LX, tester.some_elements()])
        for x, y, v in some_tuples(C, None, tester._max_runs):
            tester.assertEqual(x * (y * v) - y * (x * v), x.bracket(y) * v)

    def _subrepresentation_basis(self, gens, unitriangular=False, support_order=None):
        r"""
        Construct a basis for the subrepresentation generated by ``gens``.
        """
        G = self._g.lie_algebra_generators()
        cur = 0
        B = self.echelon_form(gens, unitriangular, order=support_order)
        while len(B) != cur:
            cur = len(B)
            B += [x * b for x in G for b in B]
            B = self.echelon_form(B, unitriangular, order=support_order)
        return B

    def subrepresentation(self, gens, unitriangular=False, support_order=None, **kwds):
        r"""
        Return the subrepresentation of ``self`` generated by ``gens``.

        .. WARNING::

            This assumes the subrepresentation is finite dimensional.
            If it is not, then this will run forever.
        """
        support_order = self._compute_support_order(gens, support_order)
        B = self._subrepresentation_basis(gens, unitriangular, support_order)
        return SubRepresentation(B, ambient=self, support_order=support_order,
                                 unitriangular=unitriangular, **kwds)

    def lie_algebra(self):
        return self._g

    class Element(CombinatorialFreeModule.Element):
        r"""
        An element of a Lie algebra representation.
        """
        def _acted_upon_(self, scalar, self_on_left=False):
            """
            Return the action of ``scalar`` on ``self``.

            EXAMPLES::

                sage: L = lie_algebras.VirasoroAlgebra(QQ)
                sage: d = L.basis()
                sage: M = L.chargeless_representation(1/2, 3/4)
                sage: x = d[-5] * M.an_element() + M.basis()[10]; x
                -9/4*v[-6] - 7/4*v[-5] - 33/4*v[-4] + v[10]
                sage: d[2] * x
                -279/16*v[-4] - 189/16*v[-3] - 759/16*v[-2] - 33/4*v[12]

                sage: v = M.basis()
                sage: all(d[i]*(d[j]*v[k]) - d[j]*(d[i]*v[k]) == d[i].bracket(d[j])*v[k]
                ....:     for i in range(-5, 5) for j in range(-5, 5) for k in range(-5, 5))
                True
            """
            P = self.parent()

            # check if it is a scalar
            temp = CombinatorialFreeModule.Element._acted_upon_(self, scalar, self_on_left)
            if temp is not None:
                return temp

            # We implement only a left action
            if not self_on_left:
                S = scalar.parent()
                if P._g.has_coerce_map_from(S):
                    scalar = P._g(scalar)
                    return self._lie_algebra_action(scalar)
                if isinstance(S, PoincareBirkhoffWittBasis) and S.lie_algebra() is P._g:
                    ret = P.zero()
                    for m, c in self._monomial_coefficients.items():
                        term = self
                        for key in reveresed(m.to_word_list()):
                            term = P._g.basis()[key] * term
                        ret += c * term
                    return ret

            # We pass it up just incase there is something else inbetween
            return super()._acted_upon_(self, scalar, self_on_left)

        def exp(self, op):
            r"""
            Return the action of the exponential of the opeartor ``op``
            on ``self``.

            .. WARNING::

                This assumes ``op`` is nilpontent on ``self``; otherwise
                this will run forever.
            """
            F = self.parent()
            ret = F.zero()
            n = 0
            temp = self
            while temp:
                ret += temp / factorial(n)
                temp = op(temp)
                n += 1
            return ret

        def _lmul_(self, other):
            return self._acted_upon_(other, self_on_left=False)

        def _rmul_(self, other):
            return self._acted_upon_(other, self_on_left=True)


# -----------------------------------------------------------------------------------------

class TensorProductRepresentation(CombinatorialFreeModule_Tensor, Representation):
    @staticmethod
    def __classcall_private__(cls, modules, **options):
        modules = sum((module._sets if isinstance(module, CombinatorialFreeModule_Tensor) else (module,) for module in modules), ())
        if any(not isinstance(M, Representation)) or any(modules[0]._g != M._g for M in modules[1:]):
            return CombinatorialFreeModule_Tensor(modules, **options)

        if all('FiniteDimensional' in M.category().axioms() for M in modules):
            options['category'] = options.pop['category'].FiniteDimensional()

        if all(isinstance(M, CrystalRepresentation):
            return TensorProductCrystalRepresentation(modules, **options)

        if isinstance(M[0], KacMoodyRepresentation):
            return KacMoodyTensorProductRepresentation(modules, **options)

        return super().__classcall__(cls, modules, **options)

    def __init__(self, modules, **options):
        CombinatorialFreeModule_Tensor.__init__(modules, **options)
        self._g = modules[0]._g

    def _action_on_basis(self, X, m):
        T = self.tensor_factors()
        ret = self.zero()
        nfactors = len(T)
        base = [M.basis()[k] for M, k in zip(T, m)]
        for i in range(nfactors):
            tp = list(base)  # make a shallow copy
            tp[i] = X * tp[i]
            ret += self._tensor_of_elements(tp)
        return ret

    class Element(Representation.Element):
        def _lie_algebra_action(self, X):
            P = self.parent()
            return P.linear_combination((P._action_on_basis(X, m), c) for m, c in self._monomial_coefficients)


Representation.Tensor = TensorProductRepresentation


class DirectSumRepresentation(CombinatorialFreeModule_CartesianProduct, Representation):
    @staticmethod
    def __classcall_private__(cls, modules, **options):
        if all(isinstance(M, CrystalRepresentation):
            return DirectSumCrystalRepresentation(modules, **options)

        if isinstance(M[0], KacMoodyRepresentation):
            return KacMoodyDirectSumRepresentation(modules, **options)

        return super().__classcall__(cls, modules, **options)

    def __init__(self, modules, **options):
        CombinatorialFreeModule_CartesianProduct.__init__(modules, **options)
        self._g = modules[0]._g

    class Element(Representation.Element):
        def _lie_algebra_action(self, X):
            P = self.parent()
            nfactors = len(P.cartesian_factors())
            return P.sum(P.cartesian_embedding(i)(X * P.cartesian_projection(i)(self))
                         for i in range(nfactors))


Representation.CartesianProduct = DirectSumRepresentation


class SubRepresentation(SubmoduleWithBasis, Representation):
    r"""
    A Lie algebra subrepresentation.
    """
    @staticmethod
    def __classcall_private__(cls, basis, ambient, unitriangular, support_order=None, **kwds):
        g = ambient.category()._g
        cat = LieAlgebraRepresentations(g).WithBasis().or_subcategory(kwds.pop("category", None))
        # FIXME: Handle the category properly (if we implement by categories)
        return super().__classcall__(cls, basis, ambient, unitriangular=unitriangular,
                                     support_order=support_order, category=cat, **kwds)

    class Element(Representation.Element):
        def _lie_algebra_action(self, scalar):
            P = self.parent()
            return P.retract(P.lift(self)._lie_algebra_action(scalar))


class TrivialRepresentation(Representation):
    r"""
    The trivial representation of a Lie algebra.
    """
    def __init__(self, g, **kwds):
        super().__init__(g, [0], **kwds)

    class Element(Representation.Element):
        def _lie_algebra_action(self, X):
            return self.parent().zero()


class AdjointRepresentation(Representation):
    r"""
    The adjoint representation of a Lie algebra.
    """
    def __init__(self, g, **kwds):
        super().__init__(g, g.indices(), **kwds)

    def from_lie_algebra(self, X):
        r"""
        Construct an element of ``self`` from the element ``X`` in the
        defining Lie algebra.
        """
        return self._from_dict(X.monomial_coefficients(copy=False),
                               remove_zeros=False, coerce=False)

    class Element(Representation.Element):
        def to_lie_algebra(self):
            r"""
            Return ``self`` as an element in the defining Lie algebra.
            """
            return self.parent()._g._from_dict(self._monomial_coefficients,
                                               remove_zeros=False, coerce=False)

        def _lie_algebra_action(self, X):
            return self.parent().from_lie_algebra(X.bracket(self.to_lie_algebra()))


# -----------------------------------------------------------------------------------------
# Representations constructed from crystals (not necessarily a q->1 global crystal basis)

class CrystalRepresentation(Representation):
    r"""
    A representation of a Kac-Moody Lie algebra whose basis is
    indexed by a crystal.
    """
    def __init__(self, g, C, category=None, **kwds):
        r"""
        Initialize ``self``.
        """
        O = CategoryO(g).WithBasis().or_subcategory(category)
        self._WLR = C.weight_lattice_realization()
        self._ac = self._WLR.simple_coroots()
        if C in Crystals().Finite():
            O = O.FiniteDimensional()
        super().__init__(self, g, C, category=O, **kwds)

    def degree_on_basis(self, b):
        return b.weight()

    def h_on_basis(self, i, b, power=1):
        return b.weight().scalar(self._ac[i]) * power


class HighestWeightCrystalRepresentation(CrystalRepresentation):
    def __init__(self, g, C, category=None, **kwds):
        O = CategoryO(g).WithBasis() & HighestWeightRepresentations(g)
        O = O.or_subcategory(category)
        return super().__init__(g, C, O, **kwds)

    def _repr_(self):
        return "V({})".format(self.highest_weight())

    def _latex_(self):
        from sage.misc.latex import latex
        return r"V\left({}\right)".format(latex(self.highest_weight()))

    def maximal_vector(self):
        return self.monomial(self.basis().keys().highest_weight_vector())

    def highest_weight(self):
        r"""
        Return the highest weight of ``self``.
        """
        return self.basis().keys().highest_weight_vector().weight()


class TensorProductCrystalRepresentation(TensorProductRepresentation):
    def __init__(self, modules, **kwds):
        indices = modules[0].basis().keys().tensor(*[M.basis().keys() for M in modules[1:]])
        CombinatorialFreeModule.__init__(self, modules[0].base_ring(), indices, **options)

    def highest_weight_subrepresentation(self, gen, C, check=True):
        r"""
        Construct a highest weight representation whose crystal is ``C``
        generated from ``gen``.
        """
        return HighestWeightCrystalSubRepresentation(gen, C, check=check)


class DirectSumCrystalRepresentation(CrystalRepresentation, DirectSumRepresentation):
    r"""
    The direct sum (cartesian product) of two representations
    constructed from crystals.
    """
    def __init__(self, modules, **kwds):
        R = modules[0].base_ring()
        self._sets = modules
        from sage.combinat.crystals.direct_sum import DirectSumOfCrystals
        indices = DirectSumOfCrystals([M.basis().keys() for M in modules], keepkey=True)
        CombinatorialFreeModule.__init__(self, R, indices, **kwds)

    def e_on_basis(self, i, b):
        ind, key = b
        return self.cartesian_embedding(ind)(self._sets.e_on_basis(i, key))

    def f_on_basis(self, i, b):
        ind, key = b
        return self.cartesian_embedding(ind)(self._sets.f_on_basis(i, key))

    class Element(CrystalRepresentation.Element, DirectSumRepresentation.Element):
        pass


class HighestWeightCrystalSubRepresentation(HighestWeightCrystalRepresentation, SubRepresentation):
    r"""
    A highest weight Lie algebra representation with a basis indexed
    by a crystal constructed as a subrepresentation.

    INPUT:

    - ``gen`` -- the generator
    - ``C`` -- the crystal basis
    - ``check`` -- verify the basis constructed really is a basis
    - ``fast_basis`` -- if ``True``, then just use the first `f_i` action to
      construct a new basis element

    EXAMPLES::

        sage: La = RootSystem(['E',6]).weight_lattice().fundamental_weights()
        sage: M = crystals.NakajimaMonomials(La[1])
        sage: VM = ReprMinuscule(M, QQ)
        sage: v = VM.maximal_vector()
        sage: x = (tensor([v, v.f(1), v.f(1).f(3)])
        ....:      - tensor([v.f(1), v, v.f(1).f(3)])
        ....:      - tensor([v, v.f(1).f(3), v.f(1)])
        ....:      + tensor([v.f(1), v.f(1).f(3), v])
        ....:      + tensor([v.f(1).f(3), v, v.f(1)])
        ....:      - tensor([v.f(1).f(3), v.f(1), v])
        ....:      )
        sage: S = SubRepresentation(x, crystals.NakajimaMonomials(La[4]))
           initializing _build_basis
           building basis
           running checks
    """
    def __init__(self, gen, C, check=True, fast_basis=True):
        if check:
            if not gen.is_highest_weight():
                raise ValueError("the generator is not a highest weight element")
            from sage.categories.highest_weight_crystals import HieghtWeightCrystals
            if C not in HieghtWeightCrystals():
                raise ValueError("the crystal must be a highest weight crystal")
            if not gen.weight() == C.highest_weight_vector().weight():
                raise ValueError("the crystal and the generator must have the same highest weight")

        if not C.is_finite():
            raise NotImplementedError("the representation must be finite dimensional")

        self._gen = gen
        self._ambient = gen.parent()
        self._d = C.cartan_type().symmetrizer()
        R = self._ambient.base_ring()
        HighestWeightCrystalRepresentation.__init__(self, R, C, prefix='s')
        self._build_basis(check=check, fast_basis=fast_basis)

    def _build_basis(self, check=True, fast_basis=True):
        # Data
        print("   initializing _build_basis")
        A = self._ambient
        R = A.base_ring()
        I = self.cartan_type().index_set()
        mg = self.basis().keys().highest_weight_vector()
        todo = set([mg])
        self._ambient_basis = {mg: self._gen}
        self._order = [mg]
        self._elements_by_weight = {mg.weight(): [mg]}
        self._support_by_weight = {mg.weight(): list(self._gen.support())}
        full_support = set(self._gen.support())
        d = self.cartan_type().symmetrizer()
        print("   building basis")
        while todo:
            x = todo.pop()
            v = self._ambient_basis[x]
            for i in I:
                y = x.f(i)
                if y is None or y in self._ambient_basis:
                    continue
                wt = y.weight()
                vp = v.f(i)

                if (not fast_basis) and full_support.issuperset(vp.support()):
                    # If there is a new support, then it must be linearly independent
                    #   from the previous weight basis elements.
                    wt_vectors = [self._ambient_basis[b] for b in self._elements_by_weight[wt]]
                    wt_vectors.append(vp)
                    M = matrix([[vec[s] for s in self._support_by_weight[wt]]
                                for vec in wt_vectors])
                    if M.rank() != M.nrows():
                        # This vector is already in the span of the weight basis
                        continue

                self._order.append(y)
                if wt in self._elements_by_weight:
                    self._elements_by_weight[wt].append(y)
                    self._support_by_weight[wt].extend(s for s in vp.support()
                                                       if s not in self._support_by_weight[wt])
                else:
                    self._elements_by_weight[wt] = [y]
                    self._support_by_weight[wt] = list(vp.support())
                full_support.update(vp.support())
                todo.add(y)
                # self._ambient_basis[y] = v.f(i)
                self._ambient_basis[y] = ~y.epsilon(i) * vp

        assert len(self._ambient_basis) == self.basis().keys().cardinality(), ("%s != %s -- missing an element in the basis"
                        % (len(self._ambient_basis), self.basis().keys().cardinality()))

        # Fix an order for the ambient support,
        #   doesn't matter which order (well, maybe computationally...)
        full_support = list(full_support)
        self._support_order = {x: i for i,x in enumerate(full_support)}

        # Safety checks (if desired)
        if not check:
            return
        print("   running checks")
        MS = MatrixSpace(R, len(self._ambient_basis), len(full_support), sparse=True)
        B = MS({(i,self._support_order[x]): coeff for i,g in enumerate(self._ambient_basis.values())
                for x,coeff in g})
        assert B.rank() == len(self._ambient_basis), (B.rank(), len(self._ambient_basis))

    def lift(self, elt):
        if not elt:
            return self._ambient.zero()
        return self._ambient.linear_combination((self._ambient_basis[i], c) for i, c in elt)

    def retract(self, vec):
        if vec == 0:
            return self.zero()
        # Since this is a weight basis and the ambient basis has the same
        #   weight as this, restrict to the ambient elements and basis elements
        #   with the same weights that appear in ``vec``.
        wts = set(x.weight() for x in vec.support())
        S = {}
        for wt in wts:
            for x in self._support_by_weight[wt]:
                S[x] = len(S)
        order = []
        for wt in wts:
            order.extend(self._elements_by_weight[wt])
        #order = [x for x in self._order if x.weight() in wts]
        MS = MatrixSpace(self.base_ring(), len(S), len(order)+1)
        mat = {(S[x],0): c for x,c in vec}
        for i, b in enumerate(order):
            for x, c in self._ambient_basis[b]:
                mat[S[x],i+1] = c
        ker = MS(mat).right_kernel_matrix(basis='echelon')
        assert ker.nrows() == 1
        ker = ker[0]
        assert ker[0] == self.base_ring().one()
        return self._from_dict({order[i-1]: -c for i,c in ker.items() if i != 0},
                               coerce=False, remove_zeros=False)

    def cartan_type(self):
        return self._ambient.cartan_type()

    @cached_method
    def e_on_basis(self, i, b):
        return self.retract(self._ambient_basis[b].e(i))

    @cached_method
    def f_on_basis(self, i, b):
        return self.retract(self._ambient_basis[b].f(i))

    def maximal_vector(self):
        return self.retract(self._gen)

    Element = ReprElement # Faster to cache the action on the basis elements


# .................

class MinusculeCrystalRepresentation(HighestWeightCrystalRepresentation):
    def e_on_basis(self, i, b):
        C = self.basis().keys()
        x = b.e(i)
        if x is None:
            return self.zero()
        return self.monomial(x)

    def f_on_basis(self, i, b):
        C = self.basis().keys()
        x = b.f(i)
        if x is None:
            return self.zero()
        return self.monomial(x)


class AdjointCrystalRepresentation(HighestWeightCrystalRepresentation):
    def __init__(self, g, C):
        self._d = C.cartan_type().symmetrizer()
        self._zero_elts = {}
        self._WLR_zero = C.weight_lattice_realization().zero()
        I = C.index_set()
        for x in C:
            if x.weight() == self._WLR_zero:
                for i in I:
                    if x.epsilon(i) > 0:
                        self._zero_elts[i] = x
                        break
        super().__init__(self, g, C)

    def e_on_basis(self, i, b):
        C = self.basis().keys()
        x = b.e(i)
        if x is None:
            return self.zero()
        I = {j: pos for pos, j in enumerate(C.index_set())}
        if x.weight() == self._WLR_zero:
            A = C.cartan_type().cartan_matrix()
            return self.monomial(x) + sum(self.term(self._zero_elts[j], -A[I[i],I[j]] / 2)
                                          for j in C.index_set()
                                          if A[I[i],I[j]] < 0 and j in self._zero_elts)
        return self.term(x, x.phi(i))

    def f_on_basis(self, i, b):
        C = self.basis().keys()
        x = b.f(i)
        if x is None:
            return self.zero()
        I = {j:pos for pos,j in enumerate(C.index_set())}
        if x.weight() == self._WLR_zero:
            A = C.cartan_type().cartan_matrix()
            return self.monomial(x) + sum(self.term(self._zero_elts[j], -A[I[i],I[j]] / 2)
                                          for j in C.index_set()
                                          if A[I[i],I[j]] < 0 and j in self._zero_elts)
        return self.term(x, x.epsilon(i))


# -----------------------------------------------------------------------------------------

class HighestWeightCrystalSubRepresentationGenericBasis(SubRepresentation):
    """
    INPUT:

    - ``gen`` -- the generator
    - ``C`` -- the crystal this is isomorphic to
    - ``check`` -- verify the basis constructed really is a basis
    - ``fast_basis`` -- if ``True``, then just use the first `f_i` action to
      construct a new basis element
    """
    def __init__(self, gen, r, s=None, q=None, check=True):
        # Something which is guaranteed to have this correct cardinality
        # This is a bit of a hack, but it will work at least.
        if s is None:
            C = r
        else:
            P = RootSystem(gen.parent().cartan_type()).weight_space()
            C = crystals.LSPaths(P(r))
        SubRepresentation.__init__(self, gen, C, check=check)

    def _build_basis(self, check=True, fast_basis=True):
        # Data
        print("   initializing _build_basis")
        A = self._ambient
        R = A.base_ring()
        I = self.cartan_type().index_set()
        mg = self.basis().keys().module_generators[0]
        todo = set([mg])
        self._ambient_basis = {mg: self._gen}
        self._order = [mg]
        self._support_by_weight = {mg.weight(): list(self._gen.support())}
        full_support = set(self._gen.support())
        d = self.cartan_type().symmetrizer()
        alpha = mg.parent().weight_lattice_realization().simple_roots()

        print("   grouping elements by weight")
        self._elements_by_weight = {}
        for rc in self.basis().keys():
            wt = rc.weight()
            if wt in self._elements_by_weight:
                self._elements_by_weight[wt].append(rc)
            else:
                self._elements_by_weight[wt] = [rc]

        wt_space_dim = {wt: 0 for wt in self._elements_by_weight}
        wt_space_dim[mg.weight()] = 1

        print("   building basis")
        #count = 0
        while todo:
            x = todo.pop()
            v = self._ambient_basis[x]
            for i in I:
                vp = v.f(i)
                if vp == 0:
                    continue
                wt = x.weight() - alpha[i]
                cur_dim = wt_space_dim[wt]

                if full_support.issuperset(vp.support()):
                    # If there is a new support, then it must be linearly independent
                    #   from the previous weight basis elements.
                    wt_vectors = [self._ambient_basis[b] for b in self._elements_by_weight[wt][:cur_dim]]
                    wt_vectors.append(vp)
                    M = matrix([[vec[s] for s in self._support_by_weight[wt]]
                                for vec in wt_vectors])
                    if M.rank() == cur_dim:
                        # This vector is already in the span of the weight basis
                        continue

                y = self._elements_by_weight[wt][cur_dim]
                self._order.append(y)
                if wt in self._support_by_weight:
                    self._support_by_weight[wt].extend(s for s in vp.support()
                                                       if s not in self._support_by_weight[wt])
                else:
                    self._support_by_weight[wt] = list(vp.support())
                full_support.update(vp.support())
                todo.add(y)
                # self._ambient_basis[y] = v.f(i)
                self._ambient_basis[y] = vp
                wt_space_dim[wt] += 1
                #count += 1
                #if count % 100 == 0:
                #    print(count)

        assert len(self._ambient_basis) == self.basis().keys().cardinality(), ("%s != %s -- missing an element in the basis"
                        % (len(self._ambient_basis), self.basis().keys().cardinality()))

        # Fix an order for the ambient support,
        #   doesn't matter which order (well, maybe computationally...)
        full_support = list(full_support)
        self._support_order = {x: i for i,x in enumerate(full_support)}

# -----------------------------------------------------------------------------------------

def path_to_seq(p, G):
    return [G.edge_label(p[i], p[i+1]) for i in range(len(p)-1)]

def apply_e(d, elt):
    for i in reversed(d):
        elt = elt.e(i)
    return elt

def apply_f(d, elt):
    for i in reversed(d):
        elt = elt.f(i)
    return elt

def gen_relations(hwd, G):
    """
    INPUT:

    - ``hwd`` -- a dict whose keys are elements of the crystal
      and whose values are the corresponding highest weight elements
    - ``G`` -- the digraph of the crystal tensor product
    """
    K = hwd.keys()
    rels = {}
    for k in K:
        for kp in K:
            if k == kp:
                continue
            p = G.shortest_path(k, kp)
            data = [G.edge_label(p[i], p[i+1]) for i in range(len(p)-1)]
            ret = hwd[k]
            for i in data:
                ret = ret.f(i)
            rels[k,kp] = ret
    return rels

def lcm_factor(factors):
    common = list(reduce(lambda x,y: x.union(y), [set(p[0] for p in f) for f in factors]))
    def find(f, x):
        for p in f:
            if p[0] == x:
                return p[1]
        return 0
    exp = [max(find(f, x) for f in factors) for x in common]
    return prod(common[i]**e for i,e in enumerate(exp))


# Use the entire crystal
def compute_highest_weight_vectors_full(V, I0, sparse=True, verbose=True):
    if verbose: print("  initializing highest weight vectors computation")
    order = V.get_order()
    R = V.base_ring()
    B = V.basis()
    if sparse:
        order_index = {k: j for j,k in enumerate(order)}
        @parallel
        def build_mat(i):
            data = {}
            for pos,k in enumerate(order):
                for kp,c in B[k].e(i).monomial_coefficients().items():
                    data[order_index[kp],pos] = c
            return matrix(data, ring=R, nrows=len(order), ncols=len(order), sparse=True)
    else:
        @parallel
        def build_mat(i):
            data = []
            for k in order:
                row = B[k].e(i)
                data += [row[kp] for kp in order]
            return matrix(data, ring=R, nrows=len(order), ncols=len(order)).transpose()

    if verbose: print("  building E action matrices")
    Emat = [out for inp,out in build_mat(list(I0))]
    if verbose: print("  stacking...")
    S = matrix.block([[Em] for Em in Emat], sparse=sparse)
    #S.change_ring(SR)
    if verbose: print("  computing kernel")
    Ker = S.right_kernel_matrix()
    #Ker = Ker.change_ring(R)
    print(Ker.rank())
    return [V.from_vector(b) for b in Ker.rows()]

# FIXME: Make the indices of a tensor product of KR modules be the
#    tensor product of KR crystals. It will make functions like this
#    require less special care!
def compute_highest_weight_vectors(V, I0, TC, sparse=True, verbose=True, brute_force=False, group_by_weight=False):
    """
    - ``V`` -- tensor product of KR modules
    - ``I0`` -- classical index set
    - ``TC`` -- tensor product of KR crystals

    OUTPUT:

    - the vectors in ``V``
    - the classically highest weight elements in ``TC``

    .. WARNING::

        The ``i``-th position in these lists do not necessarily correspond
        (although they should be the same length).
    """
    if brute_force:
        if verbose: print("  initializing highest weight vectors computation")
        order = TC.list()  # We will need this list later, so +1 for caching
        dom_wt_elts = []
        cl_hw_elts = []

        if verbose: print("  finding dominant weight elements")
        for bt in order:
            b = TC(*bt)
            wt = b.weight()
            if all(wt[i] >= 0 for i in I0):  # Assume it is expressed using fundamental weights for speed
                if all(b.e(i) is None for i in I0):
                    cl_hw_elts.append(b)
                dom_wt_elts.append(b)
        # We restrict to the weights of the highest weight elements
        highest_weights = set(b.weight() for b in cl_hw_elts)
        # Make sure cl_hw_elts are first so they become pivots
        dom_wt_elts = ([tuple(b) for b in cl_hw_elts]
                       + [tuple(b) for b in dom_wt_elts
                          if b.weight() in highest_weights and b not in cl_hw_elts])
    else:
        if verbose: print("  initializing highest weight vectors computation")
        if verbose: print("   finding I0 highest weight elements in the crystal")
        cl_hw_elts = TC.classically_highest_weight_vectors()
        dom_wt_elts = [tuple(x) for x in cl_hw_elts]  # Make sure these are first so they are pivots
        highest_weights = set(b.weight() for b in cl_hw_elts)
        def mult(C):
            ret = {}
            for x in C:
                wt = x.weight()
                if wt in ret:
                    ret[wt].append(x)
                else:
                    ret[wt] = [x]
            return ret
        if verbose: print("   computing multiplicies in tensor factors")
        mL, mR = mult(TC.crystals[0]), mult(TC.crystals[1])
        if verbose: print("  finding dominant weight elements")
        total = len(mL) * len(mR)
        div = total // 10 if total > 10 else 1
        count = 0
        for la in mL:
            for mu in mR:
                count += 1
                if count % div == 0 and verbose:
                    print("   {}".format(count * 100.0 / total))
                if la + mu not in highest_weights:
                    continue
                dom_wt_elts += [(x,y) for x in mL[la] for y in mR[mu]
                                if (x,y) not in dom_wt_elts]

    R = V.base_ring()
    B = V.basis()

    grouped_dom_wt_elts = {}
    for elt in dom_wt_elts:
        wt = elt.weight()
        if wt in grouped_dom_wt_elts:
            grouped_dom_wt_elts[wt].append(elt)
        else:
            grouped_dom_wt_elts[wt] = [elt]

    @parallel
    def compute_hw_elts(wt):
        dom_wt_elts = grouped_dom_wt_elts[wt]

        # We compute the E_i action restricted to these vectors
        if verbose: print("  {}: computing image of restricted E action of {} elements".format(wt, len(dom_wt_elts)))
        im_vecs = reduce(lambda X,Y: X.union(Y),
                         [B[k].e(i).monomial_coefficients(copy=False)
                          for k in dom_wt_elts for i in I0], set())
        im_vecs = list(im_vecs)
        if verbose: print("  {}: total support {}".format(wt, len(im_vecs)))

        if sparse:
            order_index = {k: j for j,k in enumerate(im_vecs)}
            #@parallel
            def build_mat(i):
                data = {}
                for pos,k in enumerate(dom_wt_elts):
                    for kp,c in B[k].e(i).monomial_coefficients(copy=False).items():
                        data[order_index[kp],pos] = c
                return matrix(data, ring=R, nrows=len(im_vecs), ncols=len(dom_wt_elts), sparse=True)
        else:
            #@parallel
            def build_mat(i):
                data = []
                for k in dom_wt_elts:
                    row = B[k].e(i)
                    data += [row[kp] for kp in im_vecs]
                return matrix(data, ring=R, nrows=len(dom_wt_elts), ncols=len(im_vecs)).transpose()

        if verbose: print("  {}: building E action matrices".format(wt))
        #Emat = [out for inp,out in build_mat(list(I0))]
        Emat = [build_mat(i) for i in I0]
        if verbose: print("  {}: stacking...".format(wt))
        S = matrix.block([[Em] for Em in Emat], sparse=sparse)
        #S.change_ring(SR)
        if verbose: print("  {}: computing kernel of {} matrix".format(wt, S.dimensions()))
        Ker = S.right_kernel_matrix()
        #Ker = Ker.change_ring(R)
        return Ker

    if group_by_weight:
        ret = {inp[0][0]: [V._from_dict({grouped_dom_wt_elts[inp[0][0]][i]: c for i,c in b.items()})
                           for b in Ker.rows()]
               for inp,Ker in compute_hw_elts(list(grouped_dom_wt_elts))}
        ret_hw = {wt: [] for wt in ret}
        for wt in ret:
            for x in cl_hw_elts:
                if x.weight() == wt:
                    ret_hw[wt].append(x)
        return (ret, ret_hw)

    return (sum([[V._from_dict({grouped_dom_wt_elts[inp[0][0]][i]: c for i,c in b.items()})
                  for b in Ker.rows()]
                 for inp,Ker in compute_hw_elts(list(grouped_dom_wt_elts))],
                []),
            tuple(cl_hw_elts))

    #ret_elts = []
    #for inp,Ker in compute_hw_elts(list(grouped_dom_wt_elts)):
    #    ret_elts.extend(V._from_dict({grouped_dom_wt_elts[inp[0][0]][i]: c for i,c in b.items()})
    #                    for b in Ker.rows())
    #
    #return (ret_elts, tuple(cl_hw_elts))

def build_root_paths(ct):
    """
    Return a ``dict`` of positive roots and a path of simple root operators
    to obtain the result.
    """
    ct = CartanType(ct)
    I = ct.index_set()
    Q = RootSystem(ct).root_lattice()
    Phi = set(Q.positive_roots())
    al = Q.simple_roots()
    ret = {al[i]: [i] for i in al.keys()}
    next_level = dict(ret)
    while next_level:
        cur_level = next_level
        next_level = {}
        for beta in cur_level:
            for i in I:
                gamma = beta + al[i]
                if gamma in Phi and gamma not in ret:
                    ret[gamma] = cur_level[beta] + [i]
                    next_level[gamma] = ret[gamma]
    return ret

def build_root_operators(ct):
    ct = CartanType(ct)
    paths = build_root_paths(ct)
    F = FreeMonoid(ct.index_set())
    A = F.algebra(QQ)
    x = A.algebra_generators()
    ret = {}
    for beta in paths:
        p = iter(paths[beta])
        cur = x[next(p)]
        for i in p:
            cur = cur * x[i] - x[i] * cur
        ret[beta] = [(t.to_word_list(), c) for t,c in cur]
    return ret

def apply_f_operators(ops, v):
    r"""
    Apply ``ops`` to ``v``.

    INPUT:

    - ``ops`` -- a list of pairs ``(F, c)``, where ``F`` is a list
      of indices and ``c`` is the scaling coefficient
    - ``v`` -- the vector of the representation

    OUTPUT:

    ``sum( c * F(v) for F, c in ops )``

    EXAMPLES::

        sage: # S is B(\Lambda_4) in type E_6 constructed from above
        sage: v = S.maximal_vector()
        sage: al = RootSystem(['E',6]).root_lattice().simple_roots()
        sage: b1 = al[1] + 1*al[2] + 2*al[3] + 3*al[4] + 2*al[5] + al[6]
        sage: b2 = al[1] + 2*al[2] + 2*al[3] + 3*al[4] + 2*al[5] + al[6]
        sage: ops = build_root_operators(['E',6])
        sage: vzero = apply_f_operators(ops[b2], apply_f_operators(ops[b1], v))
        sage: vzero != 0
        True

    The slow way of building the orbit (but still reasonably fast)::

        sage: orbit = set([vzero])
        sage: nl = [vzero]
        sage: I = CartanType(['E',6]).index_set()
        sage: while nl:
        ....:     cur = nl
        ....:     nl = []
        ....:     for vec in cur:
        ....:         for i in I:
        ....:             vs = vec.s(i)
        ....:             if vs in orbit or -vs in orbit:
        ....:                 continue
        ....:             orbit.add(vs)
        ....:             nl.append(vs)
        sage: len(orbit)
        240
        sage: matrix([[vec[b] for b in wt0] for vec in orbit]).rank()
        45
    """
    ret = v.parent().zero()
    for F, c in ops:
        temp = v
        for i in reversed(F):
            temp = temp.f(i)
        ret += c * temp
    return ret

