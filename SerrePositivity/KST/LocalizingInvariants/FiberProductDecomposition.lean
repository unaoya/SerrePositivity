module

public import SerrePositivity.KST.LocalizingInvariants.SplitProductEquivalence
public import SerrePositivity.KST.LocalizingInvariants.NativeFiberSequence

/-!
概要：任意の Sp fiber 四角形の coherent な切断から実 Sp 積分解を得る。
方針：三対象と両辺を保つ BF 比較に切断を移し、補正済みの積同値を戻す。
規約：積因子と元の fiber・底の同値、および元の三射への整合性を保持する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories

open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.NativeSplit

local instance nativeSplitSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance nativeSplitHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y

variable (t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle Sp.{u}) (ht : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsFiberSequence t)
  (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex t.square 1 1 ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex t.square 1 0)
  (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight t.square = 𝟙 _)

abbrev fiberIso := FiberPi.fiberIso (NativeFiber.rightMap t) (NativeFiber.asFiberSquare t ht)
abbrev totalIso := FiberPi.totalIso (NativeFiber.rightMap t) (NativeFiber.asFiberSquare t ht)
abbrev baseIso := FiberPi.baseIso (NativeFiber.rightMap t) (NativeFiber.asFiberSquare t ht)

def sectionMap := SpectrumHo.representative ((baseIso t ht).inv ≫ s ≫ (totalIso t ht).hom)

include hs in
lemma sectionMap_section : SpectrumHo.hom (sectionMap t ht s) ≫
    SpectrumHo.hom (NativeFiber.rightMap t) = 𝟙 _ := by
  rw [sectionMap, SpectrumHo.hom_representative, Category.assoc, Category.assoc,
    FiberPi.right_naturality]
  change (baseIso t ht).inv ≫ (s ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight t.square ≫ (baseIso t ht).hom)) = _
  rw [← Category.assoc s, hs, Category.id_comp, Iso.inv_hom_id]

/-- 元の fiber と底に同値な実 BF 因子の、元の Sp の実二項積。 -/
abbrev product := Binary.obj (homotopyFiber (NativeFiber.rightMap t))
  (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex t.square 1 1))

/-- 積は実際の ∞ 極限錐であり、群の積による代用ではない。 -/
def productCone := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductInfinityCone
  (homotopyFiber (NativeFiber.rightMap t)) (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex t.square 1 1))

lemma productCone_vertex : (_root_.SerrePositivity.KST.LocalizingInvariants.NativeSplit.productCone t).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (product t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex _

lemma productCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.KST.LocalizingInvariants.NativeSplit.productCone t) :=
  _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductInfinityCone_isLimit _ _

/-- 元の Sp の全空間と、元の fiber・底に同値な因子の積との同値。 -/
def equivalence : SpectrumHo.obj (product t) ≅ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex t.square 1 0 :=
  SplitProduct.equivalence (NativeFiber.rightMap t) (sectionMap t ht s)
    (sectionMap_section t ht s hs) ≪≫ (totalIso t ht).symm

lemma equivalence_inclusion : SpectrumHo.hom (Binary.inl _ _) ≫
    (equivalence t ht s hs).hom = (fiberIso t ht).inv ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom t.square := by
  change SpectrumHo.hom (Binary.inl _ _) ≫
    ((SplitProduct.equivalence _ _ _).hom ≫ (totalIso t ht).inv) = _
  rw [← Category.assoc, SplitProduct.equivalence_inclusion]
  apply (cancel_epi (fiberIso t ht).hom).mp
  rw [← Category.assoc, FiberPi.bottom_naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
  rfl

lemma equivalence_section : SpectrumHo.hom (Binary.inr _ _) ≫
    (equivalence t ht s hs).hom = (baseIso t ht).inv ≫ s := by
  change SpectrumHo.hom (Binary.inr _ _) ≫
    ((SplitProduct.equivalence _ _ _).hom ≫ (totalIso t ht).inv) = _
  rw [← Category.assoc, SplitProduct.equivalence_section, sectionMap,
    SpectrumHo.hom_representative]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

lemma equivalence_projection : (equivalence t ht s hs).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight t.square =
    SpectrumHo.hom (Binary.snd _ _) ≫ (baseIso t ht).inv := by
  have h : (totalIso t ht).inv ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight t.square =
      SpectrumHo.hom (NativeFiber.rightMap t) ≫ (baseIso t ht).inv := by
    apply (cancel_epi (totalIso t ht).hom).mp
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
      ← Category.assoc, FiberPi.right_naturality]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  change ((SplitProduct.equivalence _ _ _).hom ≫ (totalIso t ht).inv) ≫ _ = _
  rw [Category.assoc, h, ← Category.assoc, SplitProduct.equivalence_projection]

end SerrePositivity.KST.LocalizingInvariants.NativeSplit
