module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence

/-!
概要：同じ底の二つの全空間の引き戻しから、全空間 Kan 模型の積への実際の比較。
方針：元の二射影の Kan 置換を直積へまとめる。
規約：全射影と置換の単位を厳密に保持する。
使われ方：一般 coherent filtered 余極限の有限積比較の有限検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {E D B : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)

/-- 概要：fiber ごとの積の全空間の Kan 模型から元の二つの全空間模型の積への比較。
方針：元の二射影を Kan 置換で写す。
規約：実際の比較射。使われ方：filtered 有限積の交換の検査対象。 -/
def totalKanProductComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj (pullback p q) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj D :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (pullback.fst p q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (pullback.snd p q))

/-- 概要：比較は元の二射影と置換の単位を厳密に保つ。
方針：二射影と単位の自然性を使う。
規約：元の全空間を変更しない。使われ方：元の fiber の射による比較の計算。 -/
lemma totalKanProductComparison_unit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (pullback p q) ≫ totalKanProductComparison p q =
      lift (pullback.fst p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E)
        (pullback.snd p q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [totalKanProductComparison, Category.assoc, lift_fst, lift_fst,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality,
      CategoryTheory.Functor.id_map]
  · rw [totalKanProductComparison, Category.assoc, lift_snd, lift_snd,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality,
      CategoryTheory.Functor.id_map]

/-- 概要：同じ底の頂点の二つの fiber の射を元の引き戻しへまとめる。
方針：両射影が同じ定値射を被覆することを使う。
規約：元の指定二射を保つ。使われ方：積の比較への有限射の持ち上げ。 -/
def fiberPairToPullback {K : SSet.{u}} (b : B _⦋0⦌)
    (s : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) : K ⟶ pullback p q :=
  pullback.lift (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b) (by
    rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp,
      SSet.comp_const, SSet.comp_const])

/-- 概要：共通 fiber の指定二射の比較の像は元の二射の単位への合成の組。
方針：単位の比較式と引き戻しの二射影を計算する。
規約：元の二射と同じ順序。使われ方：比較ホモトピーの終点。 -/
lemma fiberPairToPullback_comparison {K : SSet.{u}} (b : B _⦋0⦌)
    (s : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) (t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) :
    (fiberPairToPullback p q b s t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (pullback p q)) ≫
      totalKanProductComparison p q =
        lift (s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app E)
          (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app D) := by
  rw [Category.assoc, totalKanProductComparison_unit, comp_lift]
  simp only [fiberPairToPullback, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]

end SerrePositivity.InfinityCategories.Project.FilteredExchange
