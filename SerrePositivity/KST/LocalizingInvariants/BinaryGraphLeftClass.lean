module

public import SerrePositivity.KST.LocalizingInvariants.BinaryGraphSquare
public import SerrePositivity.KST.LocalizingInvariants.NativeSquareRows

/-!
概要：積への包含・graph・積射を三辺に持つ正方形の左脚の類は元の b。
方針：元の正方形の可換性に第二射影を後合成し、graph の厳密な右逆則で消去する。
規約：全整数 π の検出は使わない。使われ方：元の包含に戻す境界変形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.BinaryGraph
local instance graphLeftSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
variable {T X Y Z : OmegaSpectrum.{u}} (a : T ⟶ X) (b : T ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
  (S : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ Sp.{u})
  (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ S = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.lift a b)).edge)
  (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ S = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (graph g)).edge)
  (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ S =
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (Binary.map f (𝟙 Y))).edge)

include hr in
lemma left_class : Truncated.HomotopyCategory.homMk
    (NativeSquareRows.left (Binary.lift a b) (graph g) S hb ht).toTruncated = SpectrumHo.hom b := by
  have h := NativeSquareRows.comm (Binary.lift a b) (graph g) S hb ht
  rw [NativeSquareRows.right_class _ _ _ _ _ _ hr] at h
  have hgs : SpectrumHo.hom (graph g) ≫ SpectrumHo.hom (Binary.snd Z Y) =
      𝟙 (SpectrumHo.obj Y) := by
    rw [← SpectrumHo.hom_comp, show graph g ≫ Binary.snd Z Y = 𝟙 Y from Binary.lift_snd _ _]
    exact SpectrumHo.hom_id Y
  symm
  calc
    SpectrumHo.hom b = (SpectrumHo.hom (Binary.lift a b) ≫
        SpectrumHo.hom (Binary.map f (𝟙 Y))) ≫ SpectrumHo.hom (Binary.snd Z Y) := by
      simp only [← SpectrumHo.hom_comp, Category.assoc, Binary.map_snd,
        Category.comp_id, Binary.lift_snd]
    _ = (Truncated.HomotopyCategory.homMk
        (NativeSquareRows.left (Binary.lift a b) (graph g) S hb ht).toTruncated ≫
        SpectrumHo.hom (graph g)) ≫ SpectrumHo.hom (Binary.snd Z Y) :=
      congrArg (fun t => t ≫ SpectrumHo.hom (Binary.snd Z Y)) h
    _ = _ := by
      rw [Category.assoc, hgs]
      exact Category.comp_id _

end SerrePositivity.KST.LocalizingInvariants.BinaryGraph
