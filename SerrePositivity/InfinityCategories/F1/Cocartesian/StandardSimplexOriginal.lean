module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.StandardSimplexComparison

/-!
概要：標準セル上の同じ比較を、元の大域 Hom の同じ分類作用と結ぶ。
方針：表示同型に沿う source と target の直接制限を計算し、既存の指定自然性を移す。
規約：元の全 Hom と元の標準単体を保持する。
使われ方：一次元境界と高次の面の比較を、同じ元の分類作用へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{u} C] {n : ℕ}
  (σ : (Δ[n] : SSet.{u}) ⟶ nerve C) (p q : CocartesianFibrationCategory (nerve C))
local notation "P" => cocartesianStrictTransportCoherentDiagram p.val.hom
local notation "Q" => cocartesianStrictTransportCoherentDiagram q.val.hom

/-- 同じ標準セルの source 表示変更は、元の同じ底変換作用を回収する。 -/
lemma cocartesianStandardSimplexSourceIso_original :
    cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom (Over.mk σ) ≫
      (cocartesianStandardSimplexSourceIso σ p q).hom =
    (SSet.uliftFunctor.{u + 1, u}).map
      ((cocartesianFibrationBaseChangeCoreEnriched (nerveMap (simplexNerveBaseFunctor σ))).map p q) := by
  rw [cocartesianStandardSimplexSourceIso_hom]
  exact cocartesianPullbackNativeLiftRestriction_naturality p.val.hom q.val.hom
    (simplexNerveOverIso σ).inv

/-- 同じ標準セルの target 表示変更も、元の同じ直接制限を回収する。 -/
lemma cocartesianStandardSimplexTargetIso_original :
    intervalDiagramRestriction
        ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (simplexNerveBaseFunctor σ))) P Q ≫
      (cocartesianStandardSimplexTargetIso σ p q).hom =
    intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map σ) P Q := by
  rw [cocartesianStandardSimplexTargetIso_hom]
  exact intervalDiagramOverPre_restriction P Q (uliftOverMorphism (simplexNerveOverIso σ).hom)

/-- 元の標準単体上の同じ比較は、元の大域の全 Hom 作用と指定同型で可換。 -/
def cocartesianStandardSimplexHomComparison_originalIso :
    FunctorIso
      (cocartesianPullbackNativeLiftRestriction p.val.hom q.val.hom (Over.mk σ) ≫
        cocartesianStandardSimplexHomComparison σ p q)
      (cocartesianStraighteningHomInterval p q ≫
        intervalDiagramRestriction ((SSet.uliftFunctor.{u + 1, u}).map σ) P Q) := by
  apply F2.functorIsoOfEq
    ((cocartesianBaseChangeHomNaturalityIso (simplexNerveBaseFunctor σ) p q).postcomp
      (cocartesianStandardSimplexTargetIso σ p q).hom)
  · change (_ ≫ cocartesianLocalHomComparison (simplexNerveBaseFunctor σ) p q) ≫ _ = _
    rw [← cocartesianStandardSimplexSourceIso_original σ p q]
    simp only [cocartesianStandardSimplexHomComparison, Category.assoc]
  · rw [Category.assoc, cocartesianStandardSimplexTargetIso_original]

end SerrePositivity.InfinityCategories
