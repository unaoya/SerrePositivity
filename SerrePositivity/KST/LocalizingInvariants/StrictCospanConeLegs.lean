module

public import SerrePositivity.KST.LocalizingInvariants.StrictCospanConeSquare
public import SerrePositivity.KST.LocalizingInvariants.StrictCospanConePoints

/-!
概要：通常の BF 錐の正方形表示の下辺と左辺は、元の錐の二つの射そのものである。
方針：horn の二つの頂点を strict な添字へ戻し、元の錐の各脚の等式を使う。
規約：端点・一次単体を厳密に保持。使われ方：積射影の pullback 四角形の元の四辺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.StrictCospanCone
local instance : SimplicialCategory OmegaSpectrum.{u} := OmegaSpectrum.simplicialCategory
variable {E X B : OmegaSpectrum.{u}} (f : E ⟶ B) (g : X ⟶ B)
  (c : Cone (spectrumPullbackDiagram f g))

lemma square_bottom : squareBottomEdge ≫ square f g c = SSet.yonedaEquiv.symm
    (coherentNerveEdge (c.π.app (AsSmall.up.obj WalkingCospan.left))).edge := by
  rw [square, coneSquare_bottom_leg]
  change (joinStdSimplexIso 0 0).inv ≫
    joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₀₂) ≫
      joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.inv ≫ strictCoherentConeMap c = _
  rw [← Category.assoc (joinMap _ _) (joinMap _ _), ← joinMap_comp,
    Category.id_comp, left_point]
  change strictCoherentConeLeg c (AsSmall.up.obj WalkingCospan.left) = _
  rw [strictCoherentConeLeg_eq]
  rfl

lemma square_left : squareLeftEdge ≫ square f g c = SSet.yonedaEquiv.symm
    (coherentNerveEdge (c.π.app (AsSmall.up.obj WalkingCospan.right))).edge := by
  rw [square, coneSquare_left_leg]
  change (joinStdSimplexIso 0 0).inv ≫
    joinMap (𝟙 (Δ[0] : SSet.{u + 1})) (stdSimplex.δ (1 : Fin 2) ≫ horn₂₂.ι₁₂) ≫
      joinMap (𝟙 Δ[0]) CospanShape.strictCospanHornIso.inv ≫ strictCoherentConeMap c = _
  rw [← Category.assoc (joinMap _ _) (joinMap _ _), ← joinMap_comp,
    Category.id_comp, right_point]
  change strictCoherentConeLeg c (AsSmall.up.obj WalkingCospan.right) = _
  rw [strictCoherentConeLeg_eq]
  rfl

end SerrePositivity.KST.LocalizingInvariants.StrictCospanCone
