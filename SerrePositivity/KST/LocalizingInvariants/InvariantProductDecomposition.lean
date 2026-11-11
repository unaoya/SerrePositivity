module

public import SerrePositivity.KST.LocalizingInvariants.FiberProductDecomposition
public import SerrePositivity.KST.LocalizingInvariants.InvariantPiComparison

/-!
概要：抽象 Verdier 列の局所化不変量の値が切断を持つときの実 Sp 積分解。
方針：元の値と包含・商に自然な fiber 四角形の比較で一般分裂定理を移送する。
規約：切断は h Sp の切断でよく、値の fiber 性を追加仮定にしない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant

local instance invariantSplitSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

variable {E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u} ⟶ Sp.{u}} (hE : IsLocalizingInvariant E)
  (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence.{u})
  (s : SpectrumHo.obj (value E d.right) ⟶ SpectrumHo.obj (value E d.middle))
  (hs : s ≫ SpectrumHo.hom (valueMap E d.projection) = 𝟙 _)

def fiberSection : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (hE.abstractFiberTriangle d).square 1 1 ⟶
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (hE.abstractFiberTriangle d).square 1 0 :=
  (hE.fiberRightIso d).hom ≫ s ≫ (hE.fiberMiddleIso d).inv

include hs in
lemma fiberSection_section : hE.fiberSection d s ≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (hE.abstractFiberTriangle d).square = 𝟙 _ := by
  apply (cancel_mono (hE.fiberRightIso d).hom).mp
  rw [Category.assoc, ← hE.fiber_right_naturality]
  simp only [fiberSection, Category.assoc, Iso.inv_hom_id_assoc]
  rw [hs, Category.comp_id, Category.id_comp]

def splitLeftFactorIso : SpectrumHo.obj (value E d.left) ≅ SpectrumHo.obj
    (homotopyFiber (NativeFiber.rightMap (hE.abstractFiberTriangle d))) :=
  (hE.fiberLeftIso d).symm ≪≫
    NativeSplit.fiberIso (hE.abstractFiberTriangle d) (hE.abstractFiberTriangle_isFiber d)

def splitRightFactorIso : SpectrumHo.obj (value E d.right) ≅ SpectrumHo.obj
    (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (hE.abstractFiberTriangle d).square 1 1)) :=
  (hE.fiberRightIso d).symm ≪≫
    NativeSplit.baseIso (hE.abstractFiberTriangle d) (hE.abstractFiberTriangle_isFiber d)

/-- 実 ∞ 積の頂点から元の中央の値への同値。因子の比較も元の値に取る。 -/
def splitEquivalence : SpectrumHo.obj (NativeSplit.product (hE.abstractFiberTriangle d)) ≅
    SpectrumHo.obj (value E d.middle) :=
  NativeSplit.equivalence (hE.abstractFiberTriangle d) (hE.abstractFiberTriangle_isFiber d)
    (hE.fiberSection d s) (hE.fiberSection_section d s hs) ≪≫ hE.fiberMiddleIso d

lemma splitEquivalence_inclusion : SpectrumHo.hom (Binary.inl _ _) ≫
    (hE.splitEquivalence d s hs).hom =
      (hE.splitLeftFactorIso d).inv ≫ SpectrumHo.hom (valueMap E d.inclusion) := by
  change SpectrumHo.hom (Binary.inl _ _) ≫
    ((NativeSplit.equivalence _ _ _ _).hom ≫ (hE.fiberMiddleIso d).hom) = _
  rw [← Category.assoc, NativeSplit.equivalence_inclusion, Category.assoc,
    ← hE.fiber_bottom_naturality]
  simp only [splitLeftFactorIso, Iso.trans_inv, Iso.symm_inv, Category.assoc]

lemma splitEquivalence_section : SpectrumHo.hom (Binary.inr _ _) ≫
    (hE.splitEquivalence d s hs).hom = (hE.splitRightFactorIso d).inv ≫ s := by
  change SpectrumHo.hom (Binary.inr _ _) ≫
    ((NativeSplit.equivalence _ _ _ _).hom ≫ (hE.fiberMiddleIso d).hom) = _
  rw [← Category.assoc, NativeSplit.equivalence_section]
  simp only [fiberSection, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [splitRightFactorIso, Iso.trans_inv, Iso.symm_inv, Category.assoc]

lemma splitEquivalence_projection : (hE.splitEquivalence d s hs).hom ≫
    SpectrumHo.hom (valueMap E d.projection) =
      SpectrumHo.hom (Binary.snd _ _) ≫ (hE.splitRightFactorIso d).inv := by
  change ((NativeSplit.equivalence _ _ _ _).hom ≫ (hE.fiberMiddleIso d).hom) ≫ _ = _
  rw [Category.assoc, hE.fiber_right_naturality, ← Category.assoc,
    NativeSplit.equivalence_projection]
  simp only [splitRightFactorIso, Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rfl

end SerrePositivity.KST.LocalizingInvariants.IsLocalizingInvariant
