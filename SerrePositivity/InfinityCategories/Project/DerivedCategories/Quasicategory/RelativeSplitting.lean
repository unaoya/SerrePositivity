module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeInvariant
public import SerrePositivity.KST.LocalizingInvariants.FiberProductDecomposition
public import SerrePositivity.KST.LocalizingInvariants.RelativeInvariant
public import SerrePositivity.KST.LocalizingInvariants.SpectrumProductAxes

/-!
概要：S 内で切断を持つ相対 Verdier 提示の実 Sp 積分解。
方針：S のホモトピー圏の切断を同じ E で写し、実 fiber 分裂定理を適用する。
規約：ν の像の切断から S 内の切断を推測しない。使われ方：提示つき Tamme 分裂。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra.OmegaSpectrum

open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant
end SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants

/-- 切断そのものを提示源内で指定した Verdier 四角形。 -/
structure RelativeSplitVerdierDiagram {S : SSet.{u + 1}} [Quasicategory S]
    (ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}) extends _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram ν where
  sectionHom : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex square 1 1 ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex square 1 0
  section_eq : sectionHom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight square = 𝟙 _

namespace IsRelativeLocalizingInvariant
open _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant
variable {S : SSet.{u + 1}} [Quasicategory S]
  {ν : S ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{u}} {E : S ⟶ Sp.{u}}
  (hE : IsRelativeLocalizingInvariant ν E) (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram ν)

/-- 同じ S 内の切断の E 像。 -/
def splitSection : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 1 1 ⟶
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 1 0 := (hoFunctor.map E).toFunctor.map d.sectionHom

lemma splitSection_section : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitSection (E := E) d ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight (d.square ≫ E) = 𝟙 _ := by
  change (hoFunctor.map E).toFunctor.map d.sectionHom ≫
    (hoFunctor.map E).toFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight d.square) = 𝟙 _
  rw [← CategoryTheory.Functor.map_comp, d.section_eq, CategoryTheory.Functor.map_id]

/-- 左因子は元の S 内の左頂点の E 値。 -/
def splitLeftFactorIso : SpectrumHo.obj (SpectrumHo.spectrum
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 0 0)) ≅
      SpectrumHo.obj (homotopyFiber
        (NativeFiber.rightMap (hE.fiberTriangle d.toRelativeVerdierDiagram))) :=
  SpectrumHo.spectrumIso _ ≪≫
    NativeSplit.fiberIso (hE.fiberTriangle d.toRelativeVerdierDiagram)
      (hE.fiberTriangle_isFiber d.toRelativeVerdierDiagram)

/-- 右因子も元の頂点の値から、実 fiber 比較を経て同定する。 -/
def splitRightFactorIso : SpectrumHo.obj (SpectrumHo.spectrum
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 1 1)) ≅
      SpectrumHo.obj (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 1 1)) :=
  SpectrumHo.spectrumIso _ ≪≫
    NativeSplit.baseIso (hE.fiberTriangle d.toRelativeVerdierDiagram)
      (hE.fiberTriangle_isFiber d.toRelativeVerdierDiagram)

/-- 積因子の比較は元の二頂点の値を保つ。 -/
def splitFactorComparison : SpectrumHo.obj (Binary.obj
    (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 0 0))
    (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 1 1))) ≅
      SpectrumHo.obj (NativeSplit.product (hE.fiberTriangle d.toRelativeVerdierDiagram)) :=
  Binary.mapIso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitLeftFactorIso hE) d) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitRightFactorIso hE) d)

/-- S 内の切断から、元の二因子の実 ∞ 積と元の中頂点の同値を得る。 -/
def splitComparison : SpectrumHo.obj (Binary.obj
    (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 0 0))
    (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 1 1))) ≅
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 1 0 :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitFactorComparison hE) d ≪≫
    NativeSplit.equivalence (hE.fiberTriangle d.toRelativeVerdierDiagram)
      (hE.fiberTriangle_isFiber d.toRelativeVerdierDiagram)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitSection (E := E) d) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitSection_section (E := E) d)

lemma splitComparison_inclusion : SpectrumHo.hom (Binary.inl _ _) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison hE) d).hom =
      (SpectrumHo.spectrumIso _).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (d.square ≫ E) := by
  change SpectrumHo.hom (Binary.inl _ _) ≫
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitFactorComparison hE) d).hom ≫ (NativeSplit.equivalence _ _ _ _).hom) = _
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitFactorComparison, Binary.mapIso, fiberTriangle]
  rw [← Category.assoc, Binary.hoMap_inl, Category.assoc,
    NativeSplit.equivalence_inclusion]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitLeftFactorIso, fiberTriangle, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc]

lemma splitComparison_section : SpectrumHo.hom (Binary.inr _ _) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison hE) d).hom =
      (SpectrumHo.spectrumIso _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitSection (E := E) d := by
  change SpectrumHo.hom (Binary.inr _ _) ≫
    (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitFactorComparison hE) d).hom ≫ (NativeSplit.equivalence _ _ _ _).hom) = _
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitFactorComparison, Binary.mapIso, fiberTriangle]
  rw [← Category.assoc, Binary.hoMap_inr, Category.assoc,
    NativeSplit.equivalence_section]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitRightFactorIso, fiberTriangle, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id_assoc]

lemma splitComparison_projection : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison hE) d).hom ≫
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight (d.square ≫ E) =
      SpectrumHo.hom (Binary.snd _ _) ≫ (SpectrumHo.spectrumIso _).hom := by
  change (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitFactorComparison hE) d).hom ≫ (NativeSplit.equivalence _ _ _ _).hom) ≫ _ = _
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitFactorComparison, Binary.mapIso, fiberTriangle]
  rw [Category.assoc, NativeSplit.equivalence_projection, ← Category.assoc]
  erw [Binary.hoMap_snd]
  rw [Category.assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitRightFactorIso, fiberTriangle, Iso.trans_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Tamme の C,D 順（右因子、左因子）の同値。元の値関手は E のまま。 -/
def tammeSplitComparison : SpectrumHo.obj (Binary.obj
    (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 1 1))
    (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 0 0))) ≅
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 1 0 :=
  Binary.swapIso _ _ ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison hE) d

lemma tammeSplitComparison_C : SpectrumHo.hom (Binary.inl _ _) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.tammeSplitComparison hE) d).hom =
      (SpectrumHo.spectrumIso _).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitSection (E := E) d := by
  change SpectrumHo.hom (Binary.inl _ _) ≫
    ((Binary.swapIso _ _).hom ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison hE) d).hom) = _
  rw [← Category.assoc, Binary.swapIso_inl, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison_section]

lemma tammeSplitComparison_D : SpectrumHo.hom (Binary.inr _ _) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.tammeSplitComparison hE) d).hom =
      (SpectrumHo.spectrumIso _).hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (d.square ≫ E) := by
  change SpectrumHo.hom (Binary.inr _ _) ≫
    ((Binary.swapIso _ _).hom ≫ ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison hE) d).hom) = _
  rw [← Category.assoc, Binary.swapIso_inr, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison_inclusion]

/-- 因子の積は実 ∞ 極限であり、群の積による代用ではない。 -/
def tammeProductCone := _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductInfinityCone
  (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 1 1))
  (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (d.square ≫ E) 0 0))

lemma tammeProductCone_isLimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.tammeProductCone (E := E) d) :=
  _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumBinaryProductInfinityCone_isLimit _ _

end IsRelativeLocalizingInvariant
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitComparison_inclusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison_inclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitComparison_projection := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitComparison_section := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitComparison_section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitFactorComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitFactorComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitFactorComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitLeftFactorIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitLeftFactorIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitLeftFactorIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitRightFactorIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitRightFactorIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitRightFactorIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitSection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitSection := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitSection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitSection_section := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitSection_section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.tammeProductCone (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.tammeProductCone := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.tammeProductCone

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.tammeProductCone_isLimit := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.tammeProductCone_isLimit

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.tammeSplitComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.tammeSplitComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.tammeSplitComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.tammeSplitComparison_C := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.tammeSplitComparison_C

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.tammeSplitComparison_D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.tammeSplitComparison_D

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.casesOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.mk := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.rec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.recOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.sectionHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.sectionHom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.sectionHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.section_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.section_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.toRelativeVerdierDiagram (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.toRelativeVerdierDiagram := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.toRelativeVerdierDiagram

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitLeftFactorIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitLeftFactorIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitLeftFactorIso.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitLeftFactorIso.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitRightFactorIso.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitRightFactorIso.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.IsRelativeLocalizingInvariant.splitSection._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.IsRelativeLocalizingInvariant.splitSection._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeSplitVerdierDiagram.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Quasicategory.RelativeSplitVerdierDiagram.mk.sizeOf_spec
