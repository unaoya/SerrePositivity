module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftScaffoldBaseChange

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteComparisonStep
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.LeftScaffoldPoint

/-!
概要：空でない有限鎖上の left scaffold の全空間比較。
方針：一点の場合を初期条件とし、尾部への底変換と写像円柱の帰納ステップを使う。
規約：有限鎖は ULift (Fin (n+1))、係数は Kan 複体とする。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、任意の底の標準単体への制限の比較。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：空でない有限鎖上の left scaffold の比較射は前合成同値。
方針：有限鎖の長さについて帰納し、尾部の scaffold と両端の fiber 比較を使う。
規約：始域の simplicial replacement に quasicategory 性は要求しない。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、標準単体上の scaffold 比較。 -/
lemma IsLeftScaffold.finiteComparison (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 1)))) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (F : ULift.{u} (Fin (n + 1)) ⥤ SSet.{u}) [∀ c, KanComplex (F.obj c)]
    (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.IsLeftScaffold p F l) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence l := by
  induction n generalizing E with
  | zero =>
    have : Subsingleton (ULift.{u} (Fin (0 + 1))) :=
      ⟨fun a b ↦ ULift.ext (Fin.ext (by
        have := a.down.isLt
        have := b.down.isLt
        omega))⟩
    exact hs.isPrecompositionEquivalence_of_point (ULift.up 0)
  | succ n ih =>
    obtain ⟨h, ht⟩ := hs.baseChange (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n)
    have (c : ULift.{u} (Fin (n + 1))) :
        KanComplex (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n) ⋙ F).obj c) :=
      inferInstanceAs (KanComplex (F.obj ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n).obj c)))
    exact hs.finiteComparison_step n p F l h
      (ih _ _ _ ht)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
