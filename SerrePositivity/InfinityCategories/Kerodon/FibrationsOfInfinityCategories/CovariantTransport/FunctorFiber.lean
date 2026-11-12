module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.LiftSpace

/-!
概要：fiber に値を持つ関手と内部 Hom の fiber の比較。
方針：閉構造の随伴と vertexFiber の普遍性で往復する。
規約：fiber の底は指定した頂点に厳密に固定する。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の比較を終点 fiber 内で行う準備。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：定値射による後合成は関手単体集合上でも定値。
方針：内部 Hom の自然変換を各次数・各入力で比較する。
規約：定値関手の頂点表示を用いる。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、fiber 値の関手の底の固定。 -/
lemma ihom_map_const {A X B : SSet.{u}} (b : B _⦋0⦌) :
    (ihom A).map (SSet.const b : X ⟶ B) =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const b : A ⟶ B)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro F
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：定値の関手頂点の uncurry は第一射影の後の元の関手。
方針：内部 Hom の評価で恒等射による引き戻しを計算する。
規約：A は関手の始域、L はパラメーター。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、指定した底の関手上の fiber。 -/
lemma uncurry_const_functorVertex {A L B : SSet.{u}} (f : A ⟶ B) :
    uncurry (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) : L ⟶ (ihom A).obj B) = fst A L ≫ f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  dsimp [uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex, curry', curry, SSet.unitHomEquiv, SSet.const]
  rfl

/-- 概要：vertexFiber の包含は単射。
方針：各次数で部分型の値の写像の単射性を使う。
規約：底の射に fibration 性は不要。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、fiber 値の関手の一意性の検証。 -/
instance vertexFiberι_mono {X B : SSet.{u}} (p : X ⟶ B) (b : B _⦋0⦌) :
    Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  exact Subtype.val_injective

/-- 概要：fiber 値の関手を後合成の内部 Hom の fiber に送る。
方針：fiber の包含で後合成し、その底の関手が定値であることを使う。
規約：始域 A は任意の単体集合。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、fiber 内の transport の比較。 -/
def ihomVertexFiberMap (A : SSet.{u}) {X B : SSet.{u}} (p : X ⟶ B) (b : B _⦋0⦌) :
    (ihom A).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const b : A ⟶ B)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)) (by
    rw [← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, ihom_map_const])

/-- 概要：後合成の内部 Hom の fiber を fiber 値の関手に戻す。
方針：uncurry した射を元の fiber に持ち上げ、再び curry する。
規約：底の関手は頂点 b への定値関手。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、相対的な比較を fiber の比較に移す。 -/
def ihomVertexFiberInverse (A : SSet.{u}) {X B : SSet.{u}} (p : X ⟶ B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const b : A ⟶ B)) ⟶
      (ihom A).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b
    (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const b : A ⟶ B)))) (by
      rw [← uncurry_natural_right, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, uncurry_const_functorVertex,
        SSet.comp_const]))

/-- 概要：内部 Hom の fiber を戻して包含すると元の関手となる。
方針：curry の後合成の自然性と fiber の普遍性を使う。
規約：式は単体集合の射の等式。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、fiber 比較の逆関係。 -/
lemma ihomVertexFiberInverse_comp (A : SSet.{u}) {X B : SSet.{u}} (p : X ⟶ B)
    (b : B _⦋0⦌) :
    ihomVertexFiberInverse A p b ≫ (ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const b : A ⟶ B)) := by
  unfold ihomVertexFiberInverse
  rw [← curry_natural_right, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, curry_uncurry]

/-- 概要：fiber 値の関手単体集合と後合成の内部 Hom の fiber は同型。
方針：包含による後合成と curry した fiber lift が互いに逆であることを示す。
規約：quasicategory 性や fibration 性は不要。
使われ方：Kerodon Proposition 5.2.2.8（Tag 01VS）、transport の一意性を終点 fiber 内で述べる。 -/
def ihomVertexFiberIso (A : SSet.{u}) {X B : SSet.{u}} (p : X ⟶ B) (b : B _⦋0⦌) :
    (ihom A).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const b : A ⟶ B)) where
  hom := ihomVertexFiberMap A p b
  inv := ihomVertexFiberInverse A p b
  hom_inv_id := by
    have : Mono ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b)) := inferInstance
    apply (cancel_mono ((ihom A).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b))).1
    rw [Category.assoc, ihomVertexFiberInverse_comp]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  inv_hom_id := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom A).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const b : A ⟶ B))
    unfold ihomVertexFiberMap
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.id_comp]
    exact ihomVertexFiberInverse_comp A p b

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
