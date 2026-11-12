module
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonInverseRotationPerfectBoundary
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisInverseRotationPerfectRealized

/-!
概要：元二段 Perf 包含と元負符号付き全境界を、同じ resolved 射影の固定 ν 比較へ送る。
方針：同じ実 Perf 全射を元 ν 評価で写し、保存済み全比較の残終端を保持する。
規約：元 cell 始域・元実包含・元固定 ν 比較を変更しない。
使われ方：固定 ν の上指定二単体の元全境界と共通 S 長方形の接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories

private lemma postcompBoundaryResidual
    {A X Y : SSet.{u}} [SSet.Quasicategory X] [SSet.Quasicategory Y]
    {f0 f1 f2 : A ⟶ X} {g : A ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f0 f1) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f1 f2) (b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f0 f2)
    (q : X ⟶ Y) (n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f1 ≫ q) g) (h : a ≫ e.hom = b) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f0 f1 q a ≫ n.hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f0 f2 q b ≫ ((e.postcomp q).symm.trans n).hom := by
  have hh : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f0 f1 q a ≫ (e.postcomp q).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f0 f2 q b := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed, ← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_comp, h]
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f0 f1 q a ≫ (e.postcomp q).hom) ≫
        ((e.postcomp q).symm.trans n).hom := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := by rw [hh]

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "P" => DGCategoryCellResolution.Source R (DGOdotGluing R d)
local notation "Q" => DGQuotient.QuotientObject (P)
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGOdotGluing R d)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "F" => dgOdotMilnorRightAxisQuotientSource R d
local notation "G" => dgOdotMilnorRightAxisQuotientTarget R d
local notation "τ" => dgOdotMilnorRightAxisQuotientComparison R d
local notation "RP" => dgOdotMilnorRightAxisInverseRotationPerfectRealizedFamily R d
local notation "q" => dgOdotMilnorResolvedInclusion R d
local notation "TP" => dgPerfectComparisonInverseRotationPerfectTargetFamily R (Q) (F) (G) (τ)
local notation "IP" => dgPerfectComparisonInverseRotationPerfectInr R (Q) (F) (G) (τ)
local notation "EP" => dgPerfectComparisonInverseRotationPerfectNerveComparison R (Q) (F) (G) (τ)
local notation "LB" => dgPerfectComparisonInverseRotationSignedPerfectBoundary R (Q) (F) (G) (τ)

local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnor_isDGPretriangulated R d
local instance : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (Q) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotient_isDGPretriangulated R (DGOdotGluing R d)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d)))
local notation "ν" => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.hom (dgKNativePerfectValueEquivalence R (Q))

/-- 概要：同じ元二段 Perf 右軸全族の固定 ν 評価前の指定表示。
方針：元実二段全族を同じ Milnor 入力で特殊化する。
規約：元実対象と全 Hom を保持。使われ方：ν 包含全射の始域。 -/
abbrev dgOdotMilnorRightAxisInverseRotationPerfectTargetFamily := (TP)

/-- 概要：元二段実包含の同じ固定 ν 全射。
方針：元 Perf 包含の全 native 射を同じ ν 評価へ送る。
規約：元全射を変更しない。使われ方：元指定上面の包含側境界。 -/
def dgOdotMilnorRightAxisInverseRotationNuInr :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TP) ≫ (ν)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (RP) ≫ (ν)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TP)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (RP)) (ν)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (P) (PerfectDGModule R (Q)) (IP))

/-- 概要：元負符号付き全境界の同じ固定 ν 像。
方針：元全加群射を回収する Perf 逆像に同じ評価を適用する。
規約：元長辺と元全代表評価を保持。使われ方：元上面の長辺側境界。 -/
def dgOdotMilnorRightAxisInverseRotationSignedNuBoundary :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TP) ≫ (ν)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (G) ≫ (ν)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (TP)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (G)) (ν) (LB)

/-- 概要：元二段 Perf 全比較から同じ resolved 射影の指定 ν 比較への残終端。
方針：同じ元比較の逆と保存済み指定 ν 比較を合成する。
規約：別の全比較を選ばない。使われ方：元長辺を同じ実商射影へ接続する終端。 -/
def dgOdotMilnorRightAxisInverseRotationFinalNuEvaluation :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (G) ≫ (ν))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (q) ≫ dgKNativeValueComparison R (Q)) :=
  ((EP).postcomp (ν)).symm.trans
    (dgOdotMilnorRightAxisInverseRotationRealizedNuComparison R d)

/-- 概要：元実包含と同じ resolved 射影の ν 全比較は元長辺の同じ ν 全境界と可換。
方針：元 Perf 全包含式を同じ ν 評価で写し、指定全比較の残終端を保持する。
規約：全関手射の等号であり、S 内の上二単体の存在とは区別する。
使われ方：同じ固定 ν 上面の元三境界を接続する。 -/
lemma dgOdotMilnorRightAxisInverseRotationRealizedNuComparison_inr :
    dgOdotMilnorRightAxisInverseRotationNuInr R d ≫
      (dgOdotMilnorRightAxisInverseRotationRealizedNuComparison R d).hom =
        dgOdotMilnorRightAxisInverseRotationSignedNuBoundary R d ≫
          (dgOdotMilnorRightAxisInverseRotationFinalNuEvaluation R d).hom :=
  postcompBoundaryResidual
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (P) (PerfectDGModule R (Q)) (IP)) (EP) (LB) (ν)
    (dgOdotMilnorRightAxisInverseRotationRealizedNuComparison R d)
    (dgPerfectComparisonInverseRotationPerfectNerveComparison_inr R (Q) (F) (G) (τ))
end SerrePositivity.KST.SConstruction
