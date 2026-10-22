module
public import SerrePositivity.InfinityCategories.Derived.PinchedComplexModelComparison

/-! 同じ複体の pinched 模型の対象宇宙変更は、線形成分を変えない単体的同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve.PinchedHom
open scoped Simplicial
variable {R : Type u} [CommRing R] (K : Complex R)

def dgGluingComplexPinchedUniverseEquiv (n : ℕ) :
    (complexPinchedSpace.{u, v} K) _⦋n⦌ ≃ (complexPinchedSpace.{u, w} K) _⦋n⦌ :=
  (linearEquiv (complexPinchedSource.{u, v} K) (complexPinchedTarget.{u, v} K) n).trans
    (linearEquiv (complexPinchedSource.{u, w} K) (complexPinchedTarget.{u, w} K) n).symm

lemma dgGluingComplexPinchedUniverseEquiv_linear {n : ℕ}
    (s : (complexPinchedSpace.{u, v} K) _⦋n⦌) :
    toLinearSimplex (dgGluingComplexPinchedUniverseEquiv.{u, v, w} K n s) =
      toLinearSimplex s :=
  (linearEquiv (complexPinchedSource.{u, w} K) (complexPinchedTarget.{u, w} K) n).apply_symm_apply _

def dgGluingComplexPinchedUniverseIso :
    (SSet.uliftFunctor.{max u v w, max u v}).obj (complexPinchedSpace.{u, v} K) ≅
      (SSet.uliftFunctor.{max u v w, max u w}).obj (complexPinchedSpace.{u, w} K) :=
  NatIso.ofComponents (fun n => Equiv.toIso
    { toFun := fun s =>
        ULift.up (dgGluingComplexPinchedUniverseEquiv.{u, v, w} K n.unop.len s.down)
      invFun := fun s =>
        ULift.up (dgGluingComplexPinchedUniverseEquiv.{u, w, v} K n.unop.len s.down)
      left_inv := fun s => by
        apply ULift.ext
        apply (linearEquiv (complexPinchedSource.{u, v} K)
          (complexPinchedTarget.{u, v} K) n.unop.len).injective
        change toLinearSimplex _ = toLinearSimplex s.down
        rw [dgGluingComplexPinchedUniverseEquiv_linear,
          dgGluingComplexPinchedUniverseEquiv_linear]
      right_inv := fun s => by
        apply ULift.ext
        apply (linearEquiv (complexPinchedSource.{u, w} K)
          (complexPinchedTarget.{u, w} K) n.unop.len).injective
        change toLinearSimplex _ = toLinearSimplex s.down
        rw [dgGluingComplexPinchedUniverseEquiv_linear,
          dgGluingComplexPinchedUniverseEquiv_linear] }) (by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply (linearEquiv (complexPinchedSource.{u, w} K)
      (complexPinchedTarget.{u, w} K) m.unop.len).injective
    change toLinearSimplex (dgGluingComplexPinchedUniverseEquiv.{u, v, w} K m.unop.len
      (s.down.pullback α.unop)) =
        toLinearSimplex ((dgGluingComplexPinchedUniverseEquiv.{u, v, w} K n.unop.len
          s.down).pullback α.unop)
    rw [dgGluingComplexPinchedUniverseEquiv_linear, toLinearSimplex_pullback,
      toLinearSimplex_pullback, dgGluingComplexPinchedUniverseEquiv_linear]
    rfl)

end SerrePositivity.InfinityCategories
