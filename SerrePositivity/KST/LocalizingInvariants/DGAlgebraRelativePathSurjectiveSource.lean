module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePathProjection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackComparisonQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackProjectionQuasiIso

/-!
概要：任意の次数全射代数射の相対経路の包含・両評価は準同型である。
方針：経路射の次数全射性と、底の経路対角の準同型性から pullback 比較を使う。
規約：元の底射自身の準同型性を要求しない。使われ方：平方零射影上の相対 class 模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
variable (R : Type u) [CommRing R] {C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n))

include hs in
lemma inclusion_quasiIso_of_surjective : QuasiIso (inclusion R p).hom := by
  have := pathMap_epi R p hs
  have hc := HomotopyPullbackModel.comparison_quasiIso_left R
    (Path.map R p) (Path.diagonal R B)
  have hl := HomotopyPullbackModel.left_quasiIso R
    (Path.map R p) (Path.diagonal R B) (Path.diagonal_quasiIso R B)
  have hh := quasiIso_comp _ _ (hφ := hc) (hφ' := hl)
  change QuasiIso ((HomotopyPullbackModel.comparison R _ _ ≫
    HomotopyPullbackModel.left R _ _).hom) at hh
  rw [HomotopyPullbackModel.comparison_left] at hh
  exact hh

include hs in
lemma source_quasiIso_of_surjective : QuasiIso (source R p).hom :=
  quasiIso_comp _ _ (hφ := inclusion_quasiIso_of_surjective R p hs)
    (hφ' := Path.source_quasiIso R C)

include hs in
lemma target_quasiIso_of_surjective : QuasiIso (target R p).hom := by
  have hd : QuasiIso (diagonal R p).hom := by
    have := source_quasiIso_of_surjective R p hs
    have hh : QuasiIso ((diagonal R p).hom ≫ (source R p).hom) := by
      change QuasiIso ((diagonal R p ≫ source R p).hom)
      rw [diagonal_source]
      infer_instance
    exact quasiIso_of_comp_right (diagonal R p).hom (source R p).hom
  have hh : QuasiIso ((diagonal R p).hom ≫ (target R p).hom) := by
    change QuasiIso ((diagonal R p ≫ target R p).hom)
    rw [diagonal_target]
    infer_instance
  exact quasiIso_of_comp_left (diagonal R p).hom (target R p).hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
