module

public import SerrePositivity.KST.Spectra.CoherentCospanPresentation

/-!
概要：cospan の horn 表示の二つの始点を、元の小さい通常図式の二対象へ照合する。
方針：持ち上げた nerve の零単体で二つの符号を読む。
規約：宇宙を明示し、元の頂点を保持。使われ方：strict な錐の二脚の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.StrictCospanCone

lemma left_point : (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂) ≫
    CospanShape.strictCospanHornIso.{u, u + 1}.inv = SSet.yonedaEquiv.symm
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.left))) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  apply ULift.ext
  apply ComposableArrows.ext₀
  rfl

lemma right_point : (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₁₂) ≫
    CospanShape.strictCospanHornIso.{u, u + 1}.inv = SSet.yonedaEquiv.symm
      (ULift.up (ComposableArrows.mk₀ (AsSmall.up.obj WalkingCospan.right))) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  apply ULift.ext
  apply ComposableArrows.ext₀
  rfl

end SerrePositivity.KST.LocalizingInvariants.StrictCospanCone
