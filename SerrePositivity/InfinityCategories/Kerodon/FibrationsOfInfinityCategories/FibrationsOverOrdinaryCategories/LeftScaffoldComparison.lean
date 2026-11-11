module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PrecompositionNerveLocality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldPullbackComparison

/-!
概要：通常の圏の nerve 上の left scaffold の全空間比較。
方針：底の全ての有限鎖上へ引き戻し、有限鎖での帰納と前合成同値の局所性を使う。
規約：一般の scaffold の始域に quasicategory 性を要求せず、前合成同値として結論を表す。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、left fibration の strict transport による復元。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：通常の圏の nerve 上の left scaffold の比較射は前合成同値。
方針：各有限鎖への引き戻しでの同値を示し、底についての局所性で全体へ戻す。
規約：係数値は Kan 複体、射影は left fibration。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、taut scaffold と universal scaffold の全空間比較。 -/
lemma IsLeftScaffold.isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    {p : E ⟶ nerve C} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    {F : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)]
    {l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E} (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.IsLeftScaffold p F l) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence l := by
  have h := hs.choose
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.isPrecompositionEquivalence_of_pullback_finiteNerve
    (Over.homMk (U := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)) (V := Over.mk p) l h)
    (fun n H ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.IsLeftScaffold.overPullback_finiteComparison p F l hs h n H)

/-- 概要：Kan 値図式の taut scaffold は前合成同値。
方針：係数の fiber 比較が同型である標準 scaffold に一般の全空間比較を適用する。
規約：weighted nerve は Kan 値の場合の left fibration の全空間。
使われ方：Kerodon Theorems 5.3.5.7（Tag 037Q）、5.3.5.6（Tag 037P）、weighted nerve との比較。 -/
lemma tautScaffold_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_isLeftScaffold F).isPrecompositionEquivalence

/-- 概要：left fibration の universal scaffold は前合成同値。
方針：strict transport の各係数値での評価の同値を一般の scaffold 比較に適用する。
規約：底は通常の圏の nerve。
使われ方：Kerodon Theorems 5.3.5.7（Tag 037Q）、5.3.5.6（Tag 037P）、strict transport から元の全空間の復元。 -/
lemma universalScaffold_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold p) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.universalScaffold_isLeftScaffold p).isPrecompositionEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
