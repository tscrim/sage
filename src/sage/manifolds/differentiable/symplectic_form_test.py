from _pytest.fixtures import FixtureRequest
import pytest

# TODO: Remove sage.all import as soon as it's no longer necessary to load everything upfront
import sage.all
from sage.manifolds.manifold import Manifold
from sage.manifolds.differentiable.manifold import DifferentiableManifold
from sage.manifolds.differentiable.examples.sphere import Sphere
from sage.manifolds.differentiable.symplectic_form import SymplecticForm
from sage.manifolds.differentiable.examples.symplectic_vector_space import SymplecticVectorSpace
from sage.symbolic.function_factory import function
from sage.manifolds.differentiable.scalarfield import DiffScalarField


class TestGenericSymplecticForm:

    @pytest.fixture
    def omega(self):
        # Generic 6-dimensional manifold
        M = Manifold(6, 'M')
        return SymplecticForm(M, 'omega')

    def test_repr(self, omega: SymplecticForm):
        assert str(omega) == 'Symplectic form omega on the 6-dimensional differentiable manifold M'

    def test_new_instance_repr(self, omega: SymplecticForm):
        omega1 = omega._new_instance()
        assert str(omega1) == 'Symplectic form unnamed symplectic form on the 6-dimensional differentiable manifold M'

    def test_new_instance_same_type(self, omega: SymplecticForm):
        omega1 = omega._new_instance()
        assert type(omega1) == type(omega)

    def test_new_instance_same_parent(self, omega: SymplecticForm):
        omega1 = omega._new_instance()
        assert omega1.parent() == omega.parent()


class TestCoherenceOfFormulas:
    r"""
    Test correctness of the implementation, by checking that equivalent formulas give the correct result.
    We check it for the examples of `\R^2` and `S^2`, which should be enough.
    """

    @pytest.fixture(params=["R2", "S2"])
    def M(self, request: FixtureRequest):
        if request.param == "R2":
            return SymplecticVectorSpace(2, 'R2', symplectic_name='omega')
        elif request.param == "S2":
            sphere = Sphere(2)
            # Init stereographic coordinates to get a complete atlas
            sphere.stereographic_coordinates()
            return sphere

    @pytest.fixture()
    def omega(self, M):
        if isinstance(M, SymplecticVectorSpace):
            return M.symplectic_form()
        else:
            return SymplecticForm.wrap(M.metric().volume_form(), 'omega')

    def test_flat_of_hamiltonian_vector_field(self, M: DifferentiableManifold, omega: SymplecticForm):
        H = generic_scalar_field(M, 'H')
        assert omega.flat(omega.hamiltonian_vector_field(H)) == - H.differential()

    def test_hamiltonian_vector_field_contr_symplectic_form(self, M: DifferentiableManifold, omega: SymplecticForm):
        H = generic_scalar_field(M, 'H')
        # X_H \contr \omega + \dif H = 0
        assert omega.contract(0, omega.hamiltonian_vector_field(H)) == - H.differential()

    def test_poisson_bracket_as_contraction_symplectic_form(self, M: DifferentiableManifold, omega: SymplecticForm):
        f = generic_scalar_field(M, 'f')
        g = generic_scalar_field(M, 'g')
        # {f, g} = \omega(X_f, X_g)
        assert omega.poisson_bracket(f, g) == omega.contract(0, omega.hamiltonian_vector_field(f)).contract(0, omega.hamiltonian_vector_field(g))

    def test_poisson_bracket_as_contraction_poisson_tensor(self, M: DifferentiableManifold, omega: SymplecticForm):
        f = generic_scalar_field(M, 'f')
        g = generic_scalar_field(M, 'g')
        # {f, g} = \pi(\dif f, \dif g)
        assert omega.poisson_bracket(f, g) == omega.poisson().contract(0, f.exterior_derivative()).contract(0, g.exterior_derivative())

    def test_poisson_bracket_as_contraction_hamiltonian_vector_field(self, M: DifferentiableManifold, omega: SymplecticForm):
        f = generic_scalar_field(M, 'f')
        g = generic_scalar_field(M, 'g')
        # {f, g} =  X_f (g)
        assert omega.poisson_bracket(f, g) == omega.hamiltonian_vector_field(f)(g)
        # {f, g} =  -X_g(f)
        assert omega.poisson_bracket(f, g) == - omega.hamiltonian_vector_field(g)(f)

    def test_poisson_bracket_as_commutator_hamiltonian_vector_fields(self, M: DifferentiableManifold, omega: SymplecticForm):
        f = generic_scalar_field(M, 'f')
        g = generic_scalar_field(M, 'g')
        # [X_f, X_g] = X_{{f,g}}
        assert omega.hamiltonian_vector_field(f).bracket(omega.hamiltonian_vector_field(g)) == omega.hamiltonian_vector_field(omega.poisson_bracket(f, g))


def generic_scalar_field(M: DifferentiableManifold, name: str) -> DiffScalarField:
    chart_functions = {
        chart: function(name)(*chart[:]) for chart in M.atlas()
    }
    return M.scalar_field(chart_functions, name=name)


class TestR2VectorSpace:

    @pytest.fixture
    def M(self):
        return SymplecticVectorSpace(2, 'R2', symplectic_name='omega')

    @pytest.fixture
    def omega(self, M):
        return M.symplectic_form()

    def test_display(self, omega: SymplecticForm):
        assert str(omega.display()) == r'omega = -dq∧dp'

    def test_poisson(self, omega: SymplecticForm):
        # TODO: Shouldn't this be written with wedge product?
        assert str(omega.poisson().display()) == r'poisson_omega = -e_q∧e_p'

    def test_hamiltonian_vector_field(self, M: SymplecticVectorSpace, omega: SymplecticForm):
        H = generic_scalar_field(M, 'H')
        XH = omega.hamiltonian_vector_field(H)
        assert str(XH.display()) == r'XH = d(H)/dp e_q - d(H)/dq e_p'
    
    def test_flat(self, M: SymplecticVectorSpace, omega: SymplecticForm):
        X = M.vector_field(1, 2, name='X')
        assert str(X.display()) == r'X = e_q + 2 e_p'
        assert str(omega.flat(X).display()) == r'X_flat = 2 dq - dp'

