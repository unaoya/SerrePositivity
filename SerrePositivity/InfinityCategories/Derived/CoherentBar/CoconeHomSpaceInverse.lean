module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseCoconeFamily
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseRawRecovery
/-!
概要：実 pinched Hom の全単体から、終点固定の全余錐空間への逆射を構成する。
方針：逆 HA 単体を束ねた余錐族が、全面・退化と可換であることを確認する。
規約：全次数の単体的な射として構成し、零次の逆射で代用しない。
使われ方：工程Bの写像空間全体での普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

lemma dgCoherentBarCoconeInverseSimplex_map {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearSimplex R (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) n)
    (α : Fin (m + 1) →o Fin (n + 1)) :
    dgCoherentBarCoconeInverseSimplex R D F hMC y (DGNerve.PinchedHom.LinearSimplex.pullback α f) =
      (coconeMappingSpace F y).map (SimplexCategory.mkHom α).op
        (dgCoherentBarCoconeInverseSimplex R D F hMC y f) := by
  apply dgCoherentBarCoconeFamily_ext R D F y
  intro r s
  rw [dgCoherentBarCoconeInverseSimplex_family]
  have hF := dgCoherentBarInverseSimplex_map R D F hMC
    (dgNerve.vertexEquiv R (RightModule R D) y) f s
    (OrderHom.id : Fin (r + 1) →o Fin (r + 1)) α
  have hId : SimplexCategory.mkHom (OrderHom.id : Fin (r + 1) →o Fin (r + 1)) = 𝟙 ⦋r⦌ := by
    ext i
    rfl
  rw [hId, op_id, Functor.map_id_apply] at hF
  have hC := dgCoherentBarCoconeFamilySimplex_map R D F y
    (dgCoherentBarCoconeInverseSimplex R D F hMC y f) s (𝟙 ⦋r⦌) (SimplexCategory.mkHom α)
  simp only [op_id, Functor.map_id_apply] at hC
  rw [dgCoherentBarCoconeInverseSimplex_family] at hC
  exact hF.trans hC.symm

def dgCoherentBarCoconeHomSpaceInverse :
    DGNerve.pinchedHom R (RightModule R D) (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) ⟶ coconeMappingSpace F y where
  app n := ↾fun f => dgCoherentBarCoconeInverseSimplex R D F hMC y
    (DGNerve.PinchedHom.toLinearSimplex (n := n.unop.len) f)
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro f
    change dgCoherentBarCoconeInverseSimplex R D F hMC y
      (DGNerve.PinchedHom.toLinearSimplex (f.pullback α.unop)) = _
    rw [DGNerve.PinchedHom.toLinearSimplex_pullback,
      dgCoherentBarCoconeInverseSimplex_map]
    rfl

lemma dgCoherentBarCoconeHomSpaceComparison_inverse_app {n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌) :
    (dgCoherentBarCoconeHomSpaceInverse R D F hMC y).app (Opposite.op ⦋n⦌)
      ((dgCoherentBarCoconeHomSpaceComparison R D F hMC y).app (Opposite.op ⦋n⦌) c) = c := by
  apply dgCoherentBarCoconeFamily_ext R D F y
  intro m s
  change dgCoherentBarCoconeFamilySimplex R D F y
    (dgCoherentBarCoconeInverseSimplex R D F hMC y (DGNerve.PinchedHom.toLinearSimplex
      ((dgCoherentBarCoconeHomSpaceComparison R D F hMC y).app (Opposite.op ⦋n⦌) c))) s = _
  rw [dgCoherentBarCoconeInverseSimplex_family]
  apply DGNerve.Simplex.ext
  change dgCoherentBarInverseRawData R D F hMC (dgNerve.vertexEquiv R (RightModule R D) y)
    (DGNerve.PinchedHom.toLinearData
      ((dgCoherentBarCoconeHomSpaceComparison R D F hMC y).app (Opposite.op ⦋n⦌) c)) s = _
  rw [dgCoherentBarCoconeHomSpaceComparison_linear]
  exact dgCoherentBarInverseRawData_recovery R D F hMC y c s

end SerrePositivity.InfinityCategories
