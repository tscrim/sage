r"""
Crystal of Gelfand-Tsetlin patterns

AUTHORS:

- Travis Scrimshaw: Initial version
"""

#*****************************************************************************
#       Copyright (C) 2016 Travis Scrimshaw <tscrimsh at umn.edu>
#
#  Distributed under the terms of the GNU General Public License (GPL)
#
#    This code is distributed in the hope that it will be useful,
#    but WITHOUT ANY WARRANTY; without even the implied warranty of
#    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
#    General Public License for more details.
#
#  The full text of the GPL is available at:
#
#                  http://www.gnu.org/licenses/
#****************************************************************************

from sage.combinat.root_system.cartan_type import CartanType
from sage.combinat.crystals.induced_structure import InducedCrystal
from sage.combinat.crystals.tensor_product import CrystalOfTableaux
from sage.combinat.gelfand_tsetlin_patterns import GelfandTsetlinPatterns

class CrystalOfGelfandTsetlinPatterns(InducedCrystal):
    r"""
    The crystal of Gelfand-Tsetlin patterns which is equivalent to the
    tableaux model under the bijection.

    INPUT:

    - ``n`` -- type `A_n^{(1)}`
    - ``top_row`` -- the top row which is equivalent to the dominant weight

    EXAMPLES::

        sage: C = crystals.GelfandTsetlinPatterns(2, [1])
        sage: for x in C: x.pp()
          1     0     0
             0     0
                0
          1     0     0
             1     0
                0
          1     0     0
             1     0
                1

        sage: C = crystals.GelfandTsetlinPatterns(3, [4,1,1])
        sage: mg = C.highest_weight_vector()
        sage: mg.pp()
          4     1     1     0
             4     1     1
                4     1
                   4
        sage: mg.f(2)
        sage: mg.f(3).pp()
          4     1     1     0
             4     1     0
                4     1
                   4
    """
    @staticmethod
    def __classcall_private__(cls, n, top_row):
        r"""
        Normalize input to ensure a unique representation.

        EXAMPLES::

            sage: C = crystals.GelfandTsetlinPatterns(3, [3,1,1])
            sage: C2 = crystals.GelfandTsetlinPatterns(int(3), (3,1,1,0))
            sage: C is C2
            True
        """
        top_row = list(top_row)
        if len(top_row) > n+1:
            raise ValueError("the top row can have at most %s entries"%(n+1))
        top_row += [0] * (n + 1 - len(top_row))
        if any(top_row[i+1] > top_row[i] for i in range(n)):
            raise ValueError("the top row must be non-decreasing")
        return super(CrystalOfGelfandTsetlinPatterns, cls).__classcall__(cls, n, tuple(top_row))

    def __init__(self, n, top_row):
        r"""
        Initialize ``self``.

        EXAMPLES::

            sage: C = crystals.GelfandTsetlinPatterns(2, [3,1,1])
            sage: C.category()
            Category of classical crystals
            sage: C.cartan_type()
            ['A', 2]
            sage: TestSuite(C).run()
        """
        G = GelfandTsetlinPatterns(top_row=top_row)
        self._top_row = top_row
        self._T = CrystalOfTableaux(['A', n], shape=top_row)
        InducedCrystal.__init__(self, G, self._GT_to_tableau, self._tableau_to_GT)
        gt = G([list(top_row[:i+1]) for i in reversed(range(n+1))])
        self.module_generators = (self.element_class(self, gt),)

    def _repr_(self):
        r"""
        Return a string representation of ``self``.

        EXAMPLES::

            sage: crystals.GelfandTsetlinPatterns(2, [2, 1])
            Crystal of Gelfand-Tsetlin patterns of type ['A', 2] with top row (2, 1, 0)
        """
        return "Crystal of Gelfand-Tsetlin patterns of type %s with top row %s"%(self._cartan_type, self._top_row)

    def _GT_to_tableau(self, x):
        """
        Return the Gelfand-Tsetlin pattern ``x`` as a tableau.

        EXAMPLES::

            sage: C = crystals.GelfandTsetlinPatterns(3, [2,1,1])
            sage: G = GelfandTsetlinPatterns(top_row=[2,1,1,0])
            sage: G.first().pp()
              2     1     1     0
                 1     1     0
                    1     0
                       0
            sage: C._GT_to_tableau(G.first()).pp()
              2  4
              3
              4
        """
        return self._T(x.to_tableau())

    def _tableau_to_GT(self, x):
        """
        Return the tableau ``x`` as a Gelfand-Tsetlin pattern.

        EXAMPLES::

            sage: C = crystals.GelfandTsetlinPatterns(3, [2,1,1])
            sage: T = crystals.Tableaux(['A', 3], shape=[2,1,1])
            sage: C._tableau_to_GT(T.highest_weight_vector()).pp()
              2     1     1     0
                 2     1     1
                    2     1
                       2
        """
        return self._set(x.to_tableau())

    class Element(InducedCrystal.Element):
        def pp(self):
            """
            Pretty print ``self``.

            EXAMPLES::

                sage: C = crystals.GelfandTsetlinPatterns(3, [4,3,1])
                sage: mg = C.highest_weight_vector()
                sage: mg.pp()
                  4     3     1     0
                     4     3     1
                        4     3
                           4
            """
            return self.value.pp()

