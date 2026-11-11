module
public import SerrePositivity.KST.SConstruction.PerfectInvariantFiberComparison
public import SerrePositivity.KST.LocalizingInvariants.FiberProductDecomposition

/-! # Cat^perf の実不変量値 fiber 列の積分解
概要：元の射影の値の切断から、同じ実 Sp fiber 列の積分解を得る。
方針：元の三対象と二辺の比較で切断を移し、Sp の実積分解を適用する。
規約：群の積に置換せず、元の包含・切断・射影の式を保持する。使われ方：半直交分解。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
open SerrePositivity.InfinityCategories LocalizingInvariants
open scoped Simplicial

private lemma transportedSection_hom {C : Type*} [Category C]
    {X Y Z W : C} (R : X ≅ Y) (M : Z ≅ W) (s : Y ⟶ W) :
    (R.hom ≫ s ≫ M.inv) ≫ M.hom = R.hom ≫ s := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {E : perfectStableInfinity.{u} ⟶ Sp.{u}} (hE : IsPerfectLocalizingInvariant E)
  (d : PerfectVerdierSequence.{u})
  (s : perfectInvariantHoObject E d.rightVertex ⟶
    perfectInvariantHoObject E d.middleVertex)
  (hs : s ≫ perfectInvariantHoArrow E d.projection d.middle_complete d.right_complete = 𝟙 _)

/-- 元の射影の同じ値の切断を、実 fiber 四角形の右辺の切断へ移す。 -/
def IsPerfectLocalizingInvariant.perfectFiberSection :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (hE.sequenceFiberTriangle d).square 1 1 ⟶
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (hE.sequenceFiberTriangle d).square 1 0 :=
  (hE.perfectFiberRightIso d).hom ≫ s ≫ (hE.perfectFiberMiddleIso d).inv

include hs in
/-- 移した同じ切断は、実四角形の右辺に対する切断。 -/
lemma IsPerfectLocalizingInvariant.perfectFiberSection_section :
    hE.perfectFiberSection d s ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (hE.sequenceFiberTriangle d).square = 𝟙 _ := by
  apply (cancel_mono (hE.perfectFiberRightIso d).hom).mp
  erw [Category.assoc, ← hE.perfectFiber_right_naturality]
  erw [perfectFiberSection, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    hs, Category.comp_id, Category.id_comp]

/-- 実積の左因子と、元の左端の不変量値との同じ比較。 -/
def IsPerfectLocalizingInvariant.perfectSplitLeftFactorIso :
    perfectInvariantHoObject E d.leftVertex ≅ SpectrumHo.obj
      (OmegaSpectrum.homotopyFiber (NativeFiber.rightMap (hE.sequenceFiberTriangle d))) :=
  (hE.perfectFiberLeftIso d).symm ≪≫
    NativeSplit.fiberIso (hE.sequenceFiberTriangle d) (hE.sequenceFiberTriangle_isFiber d)

/-- 実積の右因子と、元の右端の不変量値との同じ比較。 -/
def IsPerfectLocalizingInvariant.perfectSplitRightFactorIso :
    perfectInvariantHoObject E d.rightVertex ≅ SpectrumHo.obj
      (SpectrumHo.spectrum (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoVertex (hE.sequenceFiberTriangle d).square 1 1)) :=
  (hE.perfectFiberRightIso d).symm ≪≫
    NativeSplit.baseIso (hE.sequenceFiberTriangle d) (hE.sequenceFiberTriangle_isFiber d)

/-- 実 Sp 積の頂点と、元の中央の不変量値の同値。 -/
def IsPerfectLocalizingInvariant.perfectSplitEquivalence :
    SpectrumHo.obj (NativeSplit.product (hE.sequenceFiberTriangle d)) ≅
      perfectInvariantHoObject E d.middleVertex :=
  NativeSplit.equivalence (hE.sequenceFiberTriangle d) (hE.sequenceFiberTriangle_isFiber d)
    (hE.perfectFiberSection d s) (hE.perfectFiberSection_section d s hs) ≪≫
      hE.perfectFiberMiddleIso d

/-- 同じ実積分解の左包含は、元の包含の不変量値を回収する。 -/
lemma IsPerfectLocalizingInvariant.perfectSplitEquivalence_inclusion :
    SpectrumHo.hom (Binary.inl _ _) ≫ (hE.perfectSplitEquivalence d s hs).hom =
      (hE.perfectSplitLeftFactorIso d).inv ≫
        perfectInvariantHoArrow E d.verdier.inclusion d.left_complete d.middle_complete := by
  change SpectrumHo.hom (Binary.inl _ _) ≫
    ((NativeSplit.equivalence _ _ _ _).hom ≫ (hE.perfectFiberMiddleIso d).hom) = _
  erw [← Category.assoc, NativeSplit.equivalence_inclusion, Category.assoc,
    ← hE.perfectFiber_bottom_naturality]
  have hf : (hE.perfectSplitLeftFactorIso d).inv =
      (NativeSplit.fiberIso (hE.sequenceFiberTriangle d)
        (hE.sequenceFiberTriangle_isFiber d)).inv ≫ (hE.perfectFiberLeftIso d).hom := rfl
  erw [hf]
  exact (Category.assoc _ _ _).symm

/-- 同じ実積分解の右包含は、元の同じ切断を回収する。 -/
lemma IsPerfectLocalizingInvariant.perfectSplitEquivalence_section :
    SpectrumHo.hom (Binary.inr _ _) ≫ (hE.perfectSplitEquivalence d s hs).hom =
      (hE.perfectSplitRightFactorIso d).inv ≫ s := by
  change SpectrumHo.hom (Binary.inr _ _) ≫
    ((NativeSplit.equivalence _ _ _ _).hom ≫ (hE.perfectFiberMiddleIso d).hom) = _
  have hc : hE.perfectFiberSection d s ≫ (hE.perfectFiberMiddleIso d).hom =
      (hE.perfectFiberRightIso d).hom ≫ s :=
    transportedSection_hom (hE.perfectFiberRightIso d) (hE.perfectFiberMiddleIso d) s
  have hf : (hE.perfectSplitRightFactorIso d).inv =
      (NativeSplit.baseIso (hE.sequenceFiberTriangle d)
        (hE.sequenceFiberTriangle_isFiber d)).inv ≫ (hE.perfectFiberRightIso d).hom := rfl
  erw [← Category.assoc, NativeSplit.equivalence_section, Category.assoc, hc, hf]
  exact (Category.assoc _ _ _).symm

/-- 同じ実積分解の右射影は、元の完備化後の射影の不変量値を回収する。 -/
lemma IsPerfectLocalizingInvariant.perfectSplitEquivalence_projection :
    (hE.perfectSplitEquivalence d s hs).hom ≫
        perfectInvariantHoArrow E d.projection d.middle_complete d.right_complete =
      SpectrumHo.hom (Binary.snd _ _) ≫ (hE.perfectSplitRightFactorIso d).inv := by
  change ((NativeSplit.equivalence _ _ _ _).hom ≫ (hE.perfectFiberMiddleIso d).hom) ≫ _ = _
  erw [Category.assoc, hE.perfectFiber_right_naturality, ← Category.assoc,
    NativeSplit.equivalence_projection]
  have hf : (hE.perfectSplitRightFactorIso d).inv =
      (NativeSplit.baseIso (hE.sequenceFiberTriangle d)
        (hE.sequenceFiberTriangle_isFiber d)).inv ≫ (hE.perfectFiberRightIso d).hom := rfl
  erw [hf]
  exact Category.assoc _ _ _

end SerrePositivity.KST.SConstruction
