module

public import SerrePositivity.KST.LocalizingInvariants.SplitProductComparison
public import SerrePositivity.KST.LocalizingInvariants.BinaryMappingExt
public import SerrePositivity.KST.LocalizingInvariants.SpectrumZeroClass

/-!
概要：BF fiber の積比較が、元の包含と切断に両軸で一致することを示す。
方針：積への厳密な外延性と対象ごとに構成した演算の単位則を使う。
規約：射影との整合性は次の補正で得る。使われ方：coherent な分裂同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.SplitProduct

variable {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (s : Y ⟶ X)

lemma left_pair : Binary.inl (homotopyFiber f) Y ≫
    Binary.lift (Binary.fst (homotopyFiber f) Y ≫ homotopyFiberInclusion f)
      (Binary.snd (homotopyFiber f) Y ≫ s) =
    homotopyFiberInclusion f ≫ Binary.inl X X := by
  apply Binary.lift_ext <;> simp [Category.assoc]

lemma right_pair : Binary.inr (homotopyFiber f) Y ≫
    Binary.lift (Binary.fst (homotopyFiber f) Y ≫ homotopyFiberInclusion f)
      (Binary.snd (homotopyFiber f) Y ≫ s) = s ≫ Binary.inr X X := by
  apply Binary.lift_ext <;> simp [Category.assoc]

lemma comparison_left : SpectrumHo.hom (Binary.inl (homotopyFiber f) Y) ≫
    SpectrumHo.hom (comparison f s) = SpectrumHo.hom (homotopyFiberInclusion f) := by
  rw [← SpectrumHo.hom_comp]
  unfold comparison
  rw [← Category.assoc, left_pair, Category.assoc, SpectrumHo.hom_comp,
    SpectrumHo.hom_comp, Multiplication.left_hom, Category.comp_id]

lemma comparison_right : SpectrumHo.hom (Binary.inr (homotopyFiber f) Y) ≫
    SpectrumHo.hom (comparison f s) = SpectrumHo.hom s := by
  rw [← SpectrumHo.hom_comp]
  unfold comparison
  rw [← Category.assoc, right_pair, Category.assoc, SpectrumHo.hom_comp,
    SpectrumHo.hom_comp, Multiplication.right_hom, Category.comp_id]

end SerrePositivity.KST.LocalizingInvariants.SplitProduct
