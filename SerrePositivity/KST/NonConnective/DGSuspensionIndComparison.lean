module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedCompactComparison
public import SerrePositivity.KST.NonConnective.DGKappaUnconditionalStageSupply

/-!
概要：D-8 の無条件 I・P を各実懸垂段の同じ Indω／compact 比較へ代入する。
方針：固定 κ の元の反復対象と同じ段供給を使い、追加の模型を選ばない。
規約：c4・hc5・Sp 安定性を要求しない。非可算 cone の Indω 同定は主張しない。
使われ方：K-7 d4 の対象別実反復と I-2 e の無条件生成界面の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) [Fact κ.IsRegular]
  (hκ : Cardinal.aleph0 < κ) (A : PerfDGInput.{u, max (u + 1) v} R)
local notation "s" => dgKappaUnconditionalStageProvider R κ hκ
local notation "Aₙ" n => dgSuspensionIteration R s A n
local notation "Iₙ" n => DGSuspensionStageInput.cone (dgSuspensionIterationStage R s A n)
local notation "Pₙ" n => DGSuspensionStageInput.perfect (dgSuspensionIterationStage R s A n)

/-- 各段の実小核と元の実懸垂段との、追加仮定なしの Indω 同値。 -/
def dgSuspensionUnconditionalIndEquivalence (n : ℕ) :=
  dgKappaResolvedIndEquivalence R (Aₙ n) (Iₙ n) (Pₙ n)

/-- 同じ反復段の元の P／Yoneda 比較も全 Indω 上へ延長される。 -/
def dgSuspensionUnconditionalIndPIso (n : ℕ) :=
  dgKappaResolvedIndPComparisonIso R (Aₙ n) (Iₙ n) (Pₙ n)

/-- 元の指定 compact 部分どうしの実同値。 -/
def dgSuspensionUnconditionalCompactEquivalence (n : ℕ) :=
  dgKappaResolvedCompactEquivalence R (Aₙ n) (Iₙ n) (Pₙ n)

/-- 同じ Ind 同値は各実段の元の compact 包含と全関手で可換する。 -/
def dgSuspensionUnconditionalIndCompactInclusionIso (n : ℕ) :=
  dgKappaResolvedIndCompactInclusionIso R (Aₙ n) (Iₙ n) (Pₙ n)

/-- 各実反復段の compact 作用は、I-2 e の無条件安定生成界面と同じものである。 -/
theorem dgSuspensionUnconditionalCompactEquivalence_hom (n : ℕ) :
    (dgSuspensionUnconditionalCompactEquivalence R κ hκ A n).hom =
      (dgKInputStableCompactGeneration R (Aₙ n)).equivalence.inv ≫
        (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap R (Aₙ n) (Iₙ n) (Pₙ n)).hom ≫
        (dgKInputStableCompactGeneration R
          (dgKappaResolvedKernelKInput R (Aₙ n) (Iₙ n))).equivalence.hom := by
  simp only [dgSuspensionUnconditionalCompactEquivalence,
    dgKappaResolvedCompactEquivalence_hom, dgKappaResolvedCompactMoritaMap,
    dgKInputStableCompactGeneration_equivalence]

end SerrePositivity.KST.NonConnective
