module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackHomIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MarkedCocartesianFunctorFamilies

/-!
概要：局所 Hom の厳密な同型の全パラメーターでの実際の作用を計算する。
方針：全部分複体の包含で全相対 Hom の同型へ戻し、元の射への後合成を展開する。
規約：同型の順方向と逆方向の元の作用を保持する。
使われ方：制限・底変換との自然性と元の分類写像の作用の照合。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {E F B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q] (a : Over B)

/-- 同じ局所 Hom の同型は、包含後に元の全相対 Hom の pullback 同型。 -/
lemma cocartesianPullbackHomIso_hom_ι :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso p q a).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorInclusion q (pullback.snd a.hom p ≫ p)
        {e | _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst a.hom p) e} =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorInclusion (pullback.fst a.hom p) (pullback.fst a.hom q) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackRawHomIso p q a).hom :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso_hom_ι _ _ _ _

/-- 同型の順方向の全パラメーターでの展開は、元の標的への実際の後合成。 -/
lemma cocartesianPullbackHomIso_hom_uncurry {T : SSet.{u}}
    (k : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.cocartesianRelativeFunctorSpace (pullback.fst a.hom p) (pullback.fst a.hom q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry (k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso p q a).hom) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorInclusion
        (pullback.fst a.hom p) (pullback.fst a.hom q)) ≫ pullback.snd a.hom q := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry
  rw [Category.assoc, cocartesianPullbackHomIso_hom_ι, ← Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.relativeFunctorIsPullbackForward_uncurry
    (IsPullback.of_hasPullback a.hom q).flip (pullback.fst a.hom p)
    (pullback.snd a.hom p ≫ p) (by exact pullback.condition) _

/-- 同型の逆方向の族を元の標的へ写すと、指定された同じ局所 Hom の族になる。 -/
lemma cocartesianPullbackHomIso_inv_uncurry_snd {T : SSet.{u}}
    (k : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomSpace p q a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry ((k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso p q a).inv) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianRelativeFunctorInclusion (pullback.fst a.hom p) (pullback.fst a.hom q)) ≫
      pullback.snd a.hom q = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.markedCocartesianFunctorUncurry k := by
  have h := cocartesianPullbackHomIso_hom_uncurry p q a
    (k ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackHomIso p q a).inv)
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  exact h.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
