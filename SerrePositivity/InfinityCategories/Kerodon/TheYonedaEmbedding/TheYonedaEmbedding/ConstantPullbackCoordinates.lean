module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantPullbackFiber

/-!
概要：定値引き戻しと fiber・底の直積の同型の全座標を計算する。
方針：fiber と引き戻しへの持ち上げの二射影の式を使う。
規約：射影も元の fiber の包含も厳密に保持する。
使われ方：定値 unstraightening の相対射の全評価を再構成する。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

/-- 概要：定値引き戻しの fiber 座標の包含は元の第一射影。
方針：fiber の持ち上げの包含の式を使う。
規約：任意の射影。使われ方：相対射の fiber 座標の照合。 -/
lemma constantPullbackFiberIso_fst_ι {E B K : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantPullbackFiberIso (K := K) p b).hom ≫
      fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
        pullback.fst p (SSet.const b : K ⟶ B) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantPullbackFiberIso, ← Category.assoc, lift_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]

/-- 概要：定値引き戻しの逆同型の第一射影は fiber 座標の包含。
方針：引き戻しへの持ち上げを評価する。
規約：元の包含を保持。使われ方：評価を元の全空間へ戻す。 -/
lemma constantPullbackFiberIso_inv_fst {E B K : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantPullbackFiberIso (K := K) p b).inv ≫
      pullback.fst p (SSet.const b : K ⟶ B) =
        fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantPullbackFiberIso, pullback.lift_fst]

/-- 概要：定値引き戻しの逆同型の底への射影は直積の底座標。
方針：引き戻しへの持ち上げを評価する。
規約：元の底を保持。使われ方：元の底の射の再構成。 -/
lemma constantPullbackFiberIso_inv_snd {E B K : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantPullbackFiberIso (K := K) p b).inv ≫
      pullback.snd p (SSet.const b : K ⟶ B) = snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) K := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantPullbackFiberIso, pullback.lift_snd]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
