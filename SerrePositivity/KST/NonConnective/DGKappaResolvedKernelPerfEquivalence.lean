module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedEvaluationInfinity
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInfinityStableValues
public import SerrePositivity.KST.SConstruction.StableModelEquivalences

/-!
概要：同じ D-9 実小核と元の入力の固定 ν 値の、実全関手同値を供給する。
方針：同じ実評価核の ∞-Perf Morita 同値を、元の二つのラベル評価同値で挟む。
規約：明示 I・P に条件付き。固定 ν の模型を変えず、P と構造射の全入力自然性は別工程。
使われ方：K-7 c5 の既存の指定 Perf 同値欄への、同じ実評価核からの代入。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (P : DGKappaPerfectInput R D I)

/-- I・P に条件付きで、同じ実評価核から作る元の固定 ν 値同士の全写像空間の同値。 -/
def dgKappaResolvedKernelPerfQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (dgKInputStableValue R D).obj
      (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I)).obj :=
  ((presentedPerfectDGQCatEvaluationEquivalence R (dgKappaResolvedKernelKInput R D I)).trans
    ((dgKappaResolvedPerfectInfinity_isQCatEquivalence R D I P).choose.trans
      (presentedPerfectDGQCatEvaluationEquivalence R D).symm)).symm

/-- I・P に条件付きで、同じ固定 ν 値の比較は完全な順逆と元の全逆二胞体を持つ。 -/
def dgKappaResolvedKernelPerfEquivalence :
    StableModelEquivalence (stableCategoryModel (dgKInputStableValue R D))
      (stableCategoryModel (dgKInputStableValue R (dgKappaResolvedKernelKInput R D I))) := by
  let e := dgKappaResolvedKernelPerfQCatEquivalence R D I P
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact ⟨⟨e.hom, preservesCofiberData_of_isExactFunctor e.hom⟩,
    ⟨e.inv, preservesCofiberData_of_isExactFunctor e.inv⟩, e.homInvIso, e.invHomIso⟩

/-- I・P に条件付きで、供給した完全な同値の順方向は元の同じ実評価比較の逆。 -/
theorem dgKappaResolvedKernelPerfEquivalence_hom :
    (dgKappaResolvedKernelPerfEquivalence R D I P).hom.val =
      (dgKappaResolvedKernelPerfQCatEquivalence R D I P).hom := rfl

end SerrePositivity.KST.NonConnective
