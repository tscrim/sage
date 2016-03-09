r"""
Finite Weyl Groups
"""
#*****************************************************************************
#  Copyright (C) 2009    Nicolas M. Thiery <nthiery at users.sf.net>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#                  http://www.gnu.org/licenses/
#******************************************************************************

from sage.categories.category_with_axiom import CategoryWithAxiom
from sage.rings.integer import Integer

class FiniteWeylGroups(CategoryWithAxiom):
    """
    The category of finite Weyl groups.

    EXAMPLES::

        sage: C = FiniteWeylGroups()
        sage: C
        Category of finite weyl groups
        sage: C.super_categories()
        [Category of finite coxeter groups, Category of weyl groups]
        sage: C.example()
        The symmetric group on {0, ..., 3}

    TESTS::

        sage: W = FiniteWeylGroups().example()
        sage: TestSuite(W).run()
    """

    class ParentMethods:
        pass

    class ElementMethods:
        # FIXME: This is only faster in general when the Weyl group is on the ambient space
        def length(self):
            """
            Return the length of ``self``.

            Compute the length by counting the number of positive
            roots that are sent to negative roots.

            EXAMPLES::

                sage: W = WeylGroup(['D',5])
                sage: w0 = W.long_element()
                sage: w0.length()
                20
                sage: len(W.domain().positive_roots())
                20
            """
            ct = 0
            for rt in self.parent().domain().positive_roots():
                if not self.action(rt).is_positive_root():
                    ct += 1
            return Integer(ct)

