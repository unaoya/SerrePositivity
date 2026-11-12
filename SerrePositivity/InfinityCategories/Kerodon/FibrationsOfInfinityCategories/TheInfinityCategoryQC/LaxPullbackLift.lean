module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LaxPullbackProjections

/-!
概要：指定した二関手と矢印の族による lax pullback への lift。
方針：strict pullback と二因子の直積の普遍性を使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {A B C : SSet.{u}}
/-- 概要：指定した二関手と矢印の族による lax pullback への lift。
方針：strict pullback と二因子の直積の普遍性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
def laxPullbackLift {T : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
    (a : T ⟶ A) (b : T ⟶ B) (e : T ⟶ (ihom (Δ[1] : SSet.{u})).obj C)
    (hs : e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = a ≫ p)
    (ht : e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = b ≫ q) : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q :=
  pullback.lift e (CartesianMonoidalCategory.lift a b) (by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, lift_fst, tensorHom_fst]
      exact hs
    · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.arrowEndpointPair, lift_snd, tensorHom_snd]
      exact ht)
/-- 概要：指定した二関手と矢印の族による lax pullback への lift。
方針：strict pullback と二因子の直積の普遍性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
lemma laxPullbackLift_arrow {T : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
    (a : T ⟶ A) (b : T ⟶ B) (e : T ⟶ (ihom (Δ[1] : SSet.{u})).obj C)
    (hs : e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = a ≫ p)
    (ht : e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = b ≫ q) :
    laxPullbackLift p q a b e hs ht ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q = e := pullback.lift_fst _ _ _
/-- 概要：指定した二関手と矢印の族による lax pullback への lift。
方針：strict pullback と二因子の直積の普遍性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
lemma laxPullbackLift_fst {T : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
    (a : T ⟶ A) (b : T ⟶ B) (e : T ⟶ (ihom (Δ[1] : SSet.{u})).obj C)
    (hs : e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = a ≫ p)
    (ht : e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = b ≫ q) :
    laxPullbackLift p q a b e hs ht ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q = a := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst, ← Category.assoc]
  exact (congrArg (fun m ↦ m ≫ fst A B) (pullback.lift_snd _ _ _)).trans (lift_fst _ _)
/-- 概要：指定した二関手と矢印の族による lax pullback への lift。
方針：strict pullback と二因子の直積の普遍性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
lemma laxPullbackLift_snd {T : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
    (a : T ⟶ A) (b : T ⟶ B) (e : T ⟶ (ihom (Δ[1] : SSet.{u})).obj C)
    (hs : e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0) = a ≫ p)
    (ht : e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1) = b ≫ q) :
    laxPullbackLift p q a b e hs ht ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q = b := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd, ← Category.assoc]
  exact (congrArg (fun m ↦ m ≫ snd A B) (pullback.lift_snd _ _ _)).trans (lift_snd _ _)
/-- 概要：指定した二関手と矢印の族による lax pullback への lift。
方針：strict pullback と二因子の直積の普遍性を使う。
規約：矢印の向きは p(a) から q(b)。
使われ方：Tamme §1 の lax pullback と安定圏への接続。 -/
lemma laxPullback_hom_ext {T : SSet.{u}} (p : A ⟶ C) (q : B ⟶ C)
    {f g : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullback p q}
    (he : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q)
    (ha : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p q)
    (hb : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackSnd p q) : f = g := by
  apply pullback.hom_ext he
  apply CartesianMonoidalCategory.hom_ext
  · exact ha
  · exact hb

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
