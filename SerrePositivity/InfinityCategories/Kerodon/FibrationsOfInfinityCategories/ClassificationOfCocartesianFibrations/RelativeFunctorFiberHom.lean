module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：底上の相対写像空間から同じ頂点上の fiber 間の関手空間への制限。
方針：相対評価の始域を fiber に制限し、固定された底の条件で終域 fiber へ持ち上げる。
規約：射影の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、unstraightening の写像空間比較の値での作用。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：相対写像空間の普遍的な族を一つの fiber へ制限して評価する。
方針：元の全空間への評価を fiber の固定条件で持ち上げる。
規約：パラメーターは元の相対写像空間全体。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、fiber 間の Hom への作用の評価。 -/
def relativeFunctorFiberEvaluation {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q b
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (𝟙 _)) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection, ← Category.assoc,
        whiskerRight_fst, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const])

/-- 概要：相対写像空間の fiber への制限を内部 Hom の射で表す。
方針：fiber に制限した普遍的な評価を curry する。
規約：始域・標的をともに同じ b 上の fiber に制限する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、相対頂点の同型から fiber 間の関手同型への移行。 -/
def relativeFunctorFiberHom {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber q b) :=
  curry (relativeFunctorFiberEvaluation p q b)

/-- 概要：通常の底上の射の相対頂点は、fiber 間の通常の誘導射の関手頂点へ写る。
方針：部分型の包含後で、内部 Hom の各パラメーターの評価を計算する。
規約：底上の射の可換性の証明の違いには依存しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の同型を実際の fiber 射の比較へ移す。 -/
lemma relativeFunctorFiberHom_vertex {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌)
    (f : E ⟶ F) (hf : f ≫ q = p) :
    (relativeFunctorFiberHom p q b).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex q p f hf) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

/-- 概要：相対写像空間の fiber への作用を評価すると、元の族を始域 fiber に制限したもの。
方針：各次数の fiber の部分型の値を計算する。
規約：任意のパラメーター T からの族を扱う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間全体の作用と具体的な持ち上げの接続。 -/
lemma relativeFunctorFiberHom_uncurry {E F B T : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (b : B _⦋0⦌)
    (f : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace q p) :
    uncurry (f ≫ relativeFunctorFiberHom p q b) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry f := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
