module
public import SerrePositivity.KST.SConstruction.MonicKPrismNativeDirectCylinders
public import SerrePositivity.KST.SConstruction.FamilyChainCompositeDataTransport
public import SerrePositivity.KST.SConstruction.FamilyCylinderFixedBoundary

/-! # 同じ元の単一合成射から引き戻した直接補正の全木
概要：合成射の元の全補正列を先に合成し、その同じ全木を二入力パラメータへ引き戻す。
方針：元の全証人を前合成し、元の native 直接補正列と同じ端点表示へ移す。
規約：同じ全列の二つの合成木を全円柱・全二単体付きで保持する。
使われ方：異なる二入力切断で共有する合成射の直接補正を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ StableModel.{u}) {x y : I} (f : x ⟶ y)

/-- 元の単一射の全補正列を保持する同じ全合成木付き円柱。 -/
def monicKPrismUnaryCorrectionData (n : ℕ) :=
  familyChainCompositeData (monicKPrismTracedStage F f n).chain

/-- 単一射の零段の元の全補正列は空で、同じ全定数円柱を保持する。 -/
lemma monicKPrismUnaryCorrectionData_zero :
    (monicKPrismUnaryCorrectionData F f 0).homotopy.h =
      fst (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) (Δ[1] : SSet.{u}) ≫
        SSet.const (familyVertex (monicKToRawLevelMap (F.map f) 0)) :=
  familyChainCompositeData_constant_of_trace_nil _ rfl

variable {z : I} (g : y ⟶ z)

/-- 元の合成射の始点を二入力の元の同じ定数族へ表示移送する厳密な等号。 -/
lemma monicKPrismDirectCanonical_source (n : ℕ) :
    SSet.const (X := nerve (CompositionStringParameters f g))
        (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) n)) =
      nerveMap (compositionStringComposite f g) ≫ monicKPrismRawLevelFamily n F (f ≫ g) := by
  rw [monicKPrismRawLevelFamily, SSet.comp_const]

/-- 元の合成射の補正済み段を、同じ raw 評価の表示へ移す厳密な等号。 -/
lemma monicKPrismDirectCanonical_target (n : ℕ) :
    nerveMap (compositionStringComposite f g) ≫ (monicKPrismTracedStage F (f ≫ g) n).val =
      nerveMap (compositionStringComposite f g) ≫ monicKPrismTracedRawFamily F (f ≫ g) ≫
        RawSpectrumMapping.evaluation (kOmegaSpectrum (F.obj x)) (kKanSequence (F.obj z)) n := by
  rw [monicKPrismTracedRawFamily_evaluation]

/-- 同じ元の合成射の全木を先に合成して引き戻した、元の native 直接列の合成データ。 -/
def monicKPrismNativeCanonicalDirectData (n : ℕ) :
    FamilyChainCompositeData (monicKPrismNativeDirectCorrectionChain F f g n) :=
  ((monicKPrismUnaryCorrectionData F (f ≫ g) n).precomp
    (nerveMap (compositionStringComposite f g))).endpointTransport
      (monicKPrismDirectCanonical_source F f g n) (monicKPrismDirectCanonical_target F f g n)

/-- 引き戻した円柱は、元の単一合成射の同じ全円柱の実制限そのもの。 -/
lemma monicKPrismNativeCanonicalDirectData_h (n : ℕ) :
    (monicKPrismNativeCanonicalDirectData F f g n).homotopy.h =
      (nerveMap (compositionStringComposite f g) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismUnaryCorrectionData F (f ≫ g) n).homotopy.h := by
  rw [monicKPrismNativeCanonicalDirectData, FamilyChainCompositeData.endpointTransport_h,
    FamilyChainCompositeData.precomp_h]

/-- 引き戻した全三角形は、元の単一合成射の同じ全合成木の同じ像そのもの。 -/
lemma monicKPrismNativeCanonicalDirectData_triangles (n : ℕ) :
    familyChainCompositionTriangles (monicKPrismNativeCanonicalDirectData F f g n).witness =
      (familyChainCompositionTriangles (monicKPrismUnaryCorrectionData F (f ≫ g) n).witness).map
        ((nerveMap (compositionStringComposite f g) ▷ (Δ[2] : SSet.{u})) ≫ ·) := by
  rw [monicKPrismNativeCanonicalDirectData, FamilyChainCompositeData.endpointTransport_triangles,
    FamilyChainCompositeData.precomp_triangles]
  rfl

/-- 先に合成して引き戻した零段円柱全体も、元の同じ定数円柱。 -/
lemma monicKPrismNativeCanonicalDirectData_zero :
    (monicKPrismNativeCanonicalDirectData F f g 0).homotopy.h =
      fst (nerve (CompositionStringParameters f g)) (Δ[1] : SSet.{u}) ≫
        SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) 0)) := by
  rw [monicKPrismNativeCanonicalDirectData_h, monicKPrismUnaryCorrectionData_zero,
    whiskerRight_fst_assoc, SSet.comp_const]

/-- 元の native 直接円柱と先に合成して引き戻した同じ全列の円柱の実比較。 -/
def monicKPrismNativeDirectCanonicalComparison : (n : ℕ) → SSet.Homotopy
    (monicKPrismNativeDirectCorrectionData F f g n).homotopy.h
    (monicKPrismNativeCanonicalDirectData F f g n).homotopy.h := fun n =>
  match n with
  | 0 => familyHomotopyEndpointTransport
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (monicKPrismNativeDirectCorrectionData F f g 0).homotopy.h) rfl
      ((monicKPrismNativeDirectCorrectionData_zero F f g).trans
        (monicKPrismNativeCanonicalDirectData_zero F f g).symm)
  | n + 1 => familyChainCompositionComparison
      (monicKPrismNativeDirectCorrectionData F f g (n + 1)).witness
      (monicKPrismNativeCanonicalDirectData F f g (n + 1)).witness

/-- 零段の全比較自体も、元の全直接補正を全時刻固定する同じ定数円柱。 -/
lemma monicKPrismNativeDirectCanonicalComparison_zero :
    (monicKPrismNativeDirectCanonicalComparison F f g 0).h =
      fst (nerve (CompositionStringParameters f g) ⊗ (Δ[1] : SSet.{u})) Δ[1] ≫
        (monicKPrismNativeDirectCorrectionData F f g 0).homotopy.h :=
  familyHomotopyEndpointTransport_h _ _ _

/-- 比較は元の全始点族を全時刻で厳密に固定する。 -/
lemma monicKPrismNativeDirectCanonicalComparison_source (n : ℕ) :
    (SSet.ι₀ (X := nerve (CompositionStringParameters f g)) ▷ (Δ[1] : SSet.{u})) ≫
        (monicKPrismNativeDirectCanonicalComparison F f g n).h =
      fst (nerve (CompositionStringParameters f g)) Δ[1] ≫
        SSet.const (familyVertex (monicKToRawLevelMap (F.map (f ≫ g)) n)) := by
  cases n with
  | zero =>
      rw [monicKPrismNativeDirectCanonicalComparison_zero, whiskerRight_fst_assoc]
      exact congrArg (fst (nerve (CompositionStringParameters f g)) Δ[1] ≫ ·)
        (monicKPrismNativeDirectCorrectionData F f g 0).homotopy.h₀
  | succ n => exact familyChainCompositionComparison_source _ _

/-- 全区間境界も、元の全始終族のまま全比較時刻で厳密に固定する。 -/
lemma monicKPrismNativeDirectCanonicalComparison_boundary (n : ℕ) :
    ((nerve (CompositionStringParameters f g) ◁ (SSet.boundary 1).ι) ▷
        (Δ[1] : SSet.{u})) ≫ (monicKPrismNativeDirectCanonicalComparison F f g n).h =
      fst (nerve (CompositionStringParameters f g) ⊗ (∂Δ[1] : SSet.{u})) Δ[1] ≫
        (nerve (CompositionStringParameters f g) ◁ (SSet.boundary 1).ι) ≫
          (monicKPrismNativeDirectCorrectionData F f g n).homotopy.h := by
  cases n with
  | zero =>
      rw [monicKPrismNativeDirectCanonicalComparison_zero]
      exact whiskerRight_fst_assoc _ _ _
  | succ n =>
      exact familyCylinder_fixed_boundary _ (familyChainCompositionComparison_source _ _)
        (familyChainCompositionComparison_target _ _)

end SerrePositivity.KST.SConstruction
