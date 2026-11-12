module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedIndComparison

/-!
概要：同じ実小核への Indω 評価同値を、I-2 e の元の compact 包含へ照合する。
方針：無条件生成同値の実逆と同じ Yoneda 制限比較を全関手で合成する。
規約：元の compact 部分・元の包含・指定 Morita／P 比較を保持する。
使われ方：K-7 d4 の実小核比較と compact 生成元の自然性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective

variable (R : Type u) [CommRing R] (A : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R A κ) (P : DGKappaPerfectInput R A I)
local notation "B" => dgKappaResolvedKernelKInput R A I

/-- 元の I-2 e 生成同値を通る、実小核への compact 全部分圏上の作用。 -/
def dgKappaResolvedCompactMoritaMap :=
  (dgKInputCompactGenerationEquivalence R A).inv ≫
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaNativeMoritaExactMap R A I P).hom ≫
        (dgKInputCompactGenerationEquivalence R B).hom

/-- 同じ compact 作用は、実小核と元の入力の compact 部分の同値である。 -/
def dgKappaResolvedCompactEquivalence :=
  ((dgKInputCompactGenerationEquivalence R A).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsQCatEquivalence.ulift.{max (u + 1) v, max (u + 1) v + 1}
      (dgKappaResolvedKernelPerfQCatEquivalence R A I P).isQCatEquivalence).choose).trans
        (dgKInputCompactGenerationEquivalence R B)

theorem dgKappaResolvedCompactEquivalence_hom :
    (dgKappaResolvedCompactEquivalence R A I P).hom =
      dgKappaResolvedCompactMoritaMap R A I P := rfl

/-- 同じ Ind 評価同値と元の compact 包含は、全関手同型で可換する。 -/
def dgKappaResolvedIndCompactInclusionIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion Cardinal.aleph0 (dgKInputIndCompletion R A) ≫
        dgKappaResolvedIndMoritaMap R A I P)
      (dgKappaResolvedCompactMoritaMap R A I P ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion Cardinal.aleph0 (dgKInputIndCompletion R B)) := by
  let q := (dgKInputCompactGenerationEquivalence R A).inv
  let F := dgKappaResolvedIndMoritaMap R A I P
  have ej : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion Cardinal.aleph0 (dgKInputIndCompletion R A))
      (q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda Cardinal.aleph0 (dgKInputStableValue R A).obj) := by
    simpa only [Category.id_comp, q] using!
      (dgKInputCompactGeneration_familyIso R A (𝟙 _)).symm
  have e₀ := ej.postcomp F
  have e₁ := (dgKappaResolvedIndEquivalence_restrictionIso R A I P).precomp q
  have h : dgKappaResolvedCompactMoritaMap R A I P ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion Cardinal.aleph0 (dgKInputIndCompletion R B) =
        q ≫ dgKappaResolvedIndMoritaGenerator R A I P := by
    simp only [dgKappaResolvedCompactMoritaMap, Category.assoc,
      dgKInputCompactGenerationEquivalence_inclusion]
    rfl
  rw [h]
  exact (by simpa only [Category.id_comp, Category.assoc, q, F] using! e₀) ≪≫ e₁

/-- 任意の compact 入力全族でも、同じ実小核への包含比較を使う。 -/
def dgKappaResolvedIndCompactParameterIso
    {T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{max (u + 1) v, max (u + 1) v + 1}
      Cardinal.aleph0 (dgKInputIndCompletion R A)) :=
  (dgKappaResolvedIndCompactInclusionIso R A I P).precomp a

/-- 比較の再制限は全次数で元のパラメータ合成と厳密に一致する。 -/
theorem dgKappaResolvedIndCompactParameterIso_precomp
    {S T : SSet.{max (u + 1) v + 1}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{max (u + 1) v, max (u + 1) v + 1}
      Cardinal.aleph0 (dgKInputIndCompletion R A))
    (r : S ⟶ T) :
    (dgKappaResolvedIndCompactParameterIso R A I P a).precomp r =
      dgKappaResolvedIndCompactParameterIso R A I P (r ≫ a) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp _ _ _

end SerrePositivity.KST.NonConnective
