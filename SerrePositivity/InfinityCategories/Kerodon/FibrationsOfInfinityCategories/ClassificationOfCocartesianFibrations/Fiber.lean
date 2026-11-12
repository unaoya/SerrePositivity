module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：頂点 fiber の宇宙持ち上げと、持ち上げた射の fiber の厳密な同型。
方針：ULift と fiber の部分型を各次数で入れ替える。
規約：射影の充填性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、weighted nerve と coherent な復元の fiber の宇宙を揃える。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：頂点 fiber を宇宙持ち上げしてから、持ち上げた射の fiber に写す。
方針：fiber の元の ULift を部分型の値へ移す。
規約：底の頂点は同じ b の ULift。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、fiber と空間値の持ち上げの接続。 -/
def uliftVertexFiberMap {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b) where
  app d := ↾fun x ↦ ⟨ULift.up x.down.val, congrArg ULift.up x.down.property⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl

/-- 概要：持ち上げた射の fiber から、元の fiber の宇宙持ち上げへ戻す。
方針：部分型の値の ULift を取り出し、底の条件を ULift.down で戻す。
規約：元の底の頂点 b を保つ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、fiber の宇宙移送の逆射。 -/
def uliftVertexFiberInverse {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b) ⟶
      (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) where
  app d := ↾fun x ↦ ULift.up ⟨x.val.down, congrArg ULift.down x.property⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    rfl

/-- 概要：fiber と宇宙持ち上げは厳密な同型で可換。
方針：各次数で ULift と部分型の往復を計算する。
規約：追加の宇宙 v は任意。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元比較の fiber を元の係数の宇宙持ち上げと比較する。 -/
def uliftVertexFiberIso {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b) where
  hom := uliftVertexFiberMap p b
  inv := uliftVertexFiberInverse p b
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    apply Subtype.ext
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    apply ULift.ext
    rfl

/-- 概要：fiber の宇宙移送の順方向は全空間への包含と可換。
方針：各次数の部分型の値を計算する。
規約：全空間への射も同じ宇宙持ち上げで写す。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、持ち上げた transport の始点・終点の条件。 -/
lemma uliftVertexFiberIso_hom_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (uliftVertexFiberIso.{u, v} p b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b) =
        (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := rfl

/-- 概要：fiber の宇宙移送の逆方向も全空間への包含と可換。
方針：部分型の値から取り出した ULift を計算する。
規約：持ち上げた元の fiber の包含を使う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、持ち上げた prism の初期値の計算。 -/
lemma uliftVertexFiberIso_inv_ι {E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (uliftVertexFiberIso.{u, v} p b).inv ≫
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((SSet.uliftFunctor.{v, u}).map p) (ULift.up b) := rfl

/-- 概要：fiber の宇宙移送は底上の射による fiber の誘導射と可換。
方針：各次数で、同じ全空間の射を同じ部分型の値に適用することを確認する。
規約：底の可換性は持ち上げる前に指定する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、復元比較の値での自然性の宇宙調整。 -/
lemma uliftVertexFiberIso_naturality {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (f : E ⟶ F) (hf : f ≫ q = p) (b : B _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b) ≫
      (uliftVertexFiberIso.{u, v} q b).hom =
    (uliftVertexFiberIso.{u, v} p b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap ((SSet.uliftFunctor.{v, u}).map p) ((SSet.uliftFunctor.{v, u}).map q)
        ((SSet.uliftFunctor.{v, u}).map f) (by
          rw [← Functor.map_comp, hf]) (ULift.up b) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
