module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLinearEquation
/-!
概要：固定終点の全余錐空間から、正規化実 bar を始域とする実 pinched Hom への射を構成する。
方針：全部分集合の線形解を既存の pinched 単体へ戻し、全単調写像の自然性で束ねる。
規約：ここでは射を構成し、同値性は後続で検証する。
使われ方：工程Bの写像空間全体での普遍性比較。
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

def dgCoherentBarCoconePinchedSimplex {n : ℕ} (c : (coconeMappingSpace F y) _⦋n⦌) :
    (DGNerve.pinchedHom R (RightModule R D) (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y)) _⦋n⦌ :=
  DGNerve.PinchedHom.LinearSimplex.toPinched (dgCoherentBarCoconeLinearSimplex R D F hMC y c)

lemma dgCoherentBarCoconePinchedSimplex_map {m n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌) (α : Fin (m + 1) →o Fin (n + 1)) :
    dgCoherentBarCoconePinchedSimplex R D F hMC y
      ((coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c) =
    (dgCoherentBarCoconePinchedSimplex R D F hMC y c).pullback (SimplexCategory.mkHom α) := by
  apply (DGNerve.PinchedHom.linearEquiv
    (dgCoherentBarNormalizedModule R D F hMC)
    (dgNerve.vertexEquiv R (RightModule R D) y) m).injective
  change DGNerve.PinchedHom.toLinearSimplex
    (dgCoherentBarCoconePinchedSimplex R D F hMC y
      ((coconeMappingSpace F y).map (SimplexCategory.mkHom α).op c)) =
    DGNerve.PinchedHom.toLinearSimplex
      ((dgCoherentBarCoconePinchedSimplex R D F hMC y c).pullback (SimplexCategory.mkHom α))
  unfold dgCoherentBarCoconePinchedSimplex
  rw [DGNerve.PinchedHom.LinearSimplex.toLinearSimplex_toPinched,
    DGNerve.PinchedHom.toLinearSimplex_pullback,
    DGNerve.PinchedHom.LinearSimplex.toLinearSimplex_toPinched,
    dgCoherentBarCoconeLinearSimplex_map]
  rfl

def dgCoherentBarCoconeHomSpaceComparison : coconeMappingSpace F y ⟶
    DGNerve.pinchedHom R (RightModule R D) (dgCoherentBarNormalizedModule R D F hMC)
      (dgNerve.vertexEquiv R (RightModule R D) y) where
  app n := ↾fun c => dgCoherentBarCoconePinchedSimplex R D F hMC y (n := n.unop.len) c
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    intro c
    exact dgCoherentBarCoconePinchedSimplex_map R D F hMC y c α.unop.toOrderHom

lemma dgCoherentBarCoconeHomSpaceComparison_linear {n : ℕ}
    (c : (coconeMappingSpace F y) _⦋n⦌) :
    DGNerve.PinchedHom.toLinearData
      ((dgCoherentBarCoconeHomSpaceComparison R D F hMC y).app (Opposite.op ⦋n⦌) c) =
      dgCoherentBarCoconeLinearData R D F hMC y c :=
  congrArg Subtype.val (DGNerve.PinchedHom.LinearSimplex.toLinearSimplex_toPinched
    (dgCoherentBarCoconeLinearSimplex R D F hMC y c))

abbrev dgCoherentBarCoconeHomSpaceComparisonUnconditional : coconeMappingSpace F y ⟶
    DGNerve.pinchedHom R (RightModule R D)
      (dgCoherentBarNormalizedModule R D F (dgCoherentBarTheta_maurerCartan R D F))
      (dgNerve.vertexEquiv R (RightModule R D) y) :=
  dgCoherentBarCoconeHomSpaceComparison R D F (dgCoherentBarTheta_maurerCartan R D F) y

end SerrePositivity.InfinityCategories
