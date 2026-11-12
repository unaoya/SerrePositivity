module
public import SerrePositivity.KST.SConstruction.FunctorStability
public import SerrePositivity.KST.SConstruction.ExactMaps

/-! # 関手圏の制限と後合成の cofiber 保存
概要：関手圏の添字制限と零対象・押し出しを保つ射の後合成は cofiber を保つ。
方針：零角の四角形を点ごとに評価し、A6 で普遍性を戻す。
規約：任意の押し出しに対する保存とは区別する。使われ方：反復 S• の普遍性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：内部 Hom の後合成と頂点評価は可換。
方針：全単体で評価の定義を計算する。
規約：quasicategory 性は不要。使われ方：点ごとの保存性。 -/
lemma ihom_postcomp_evaluate {A C D : SSet.{u}} (f : C ⟶ D) (a : A _⦋0⦌) :
    (ihom A).map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a ≫ f := rfl

/-- 概要：関手圏の添字制限は零対象を保存する。
方針：評価との可換性と点ごとの零対象判定を使う。
規約：標的は零対象を持つ quasicategory。使われ方：制限した零角。 -/
lemma functor_reindex_isZeroVertex {A B C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C]
    (i : A ⟶ B) {v : ((ihom B).obj C) _⦋0⦌} (hv : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((pre i).app C).app (Opposite.op ⦋0⦌) v) := by
  apply isZeroVertex_of_pointwise
  intro a
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((pre i).app C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app (Opposite.op ⦋0⦌) v)
  rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  exact isZeroVertex_evaluateFunctorAt hv _

/-- 概要：関手圏の後合成は零対象を保存する。
方針：各評価の零対象性に入力の零対象保存を適用する。
規約：chosen zero の厳密な保存は不要。使われ方：後合成した零角。 -/
lemma functor_postcomp_isZeroVertex {A C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
    [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex C] (f : C ⟶ D)
    (hf : ∀ z, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z → _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (f.app (Opposite.op ⦋0⦌) z))
    {v : ((ihom A).obj C) _⦋0⦌} (hv : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex v) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((ihom A).map f).app (Opposite.op ⦋0⦌) v) := by
  apply isZeroVertex_of_pointwise
  intro a
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((ihom A).map f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app (Opposite.op ⦋0⦌) v)
  rw [ihom_postcomp_evaluate]
  exact hf _ (isZeroVertex_evaluateFunctorAt hv a)

/-- 概要：安定な標的の関手圏の添字制限は cofiber 正方形を保存する。
方針：零角つきの押し出しを点ごとに評価してから制限する。
規約：入力は ZeroTriangle、任意の押し出しへの主張ではない。
使われ方：cofiber の族のパラメーター変更。 -/
lemma functor_reindex_preserves_cofiber {A B C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    (i : A ⟶ B) (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle ((ihom B).obj C)) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t.square ≫ (pre i).app C) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPushoutSquare_of_pointwise
  intro a
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt]
  exact (functor_zeroTriangle_pushout_iff t).1 ht _

/-- 概要：保存条件を持つ射の関手圏での後合成は cofiber 正方形を保存する。
方針：元の四角形を点ごとの押し出しに直し、保存後に点ごとの判定で戻す。
規約：標的 D には quasicategory 性だけを要求する。
使われ方：cofiber の族に対する関手性。 -/
lemma functor_postcomp_preserves_cofiber {A C D : SSet.{u}}
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [Quasicategory D]
    (f : C ⟶ D) (hf : PreservesSConstructionData f)
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle ((ihom A).obj C)) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (t.square ≫ (ihom A).map f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPushoutSquare_of_pointwise
  intro a
  rw [Category.assoc, ihom_postcomp_evaluate, ← Category.assoc]
  exact hf.2 _ ((functor_zeroTriangle_pushout_iff t).1 ht a)

end SerrePositivity.KST.SConstruction
