module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-!
概要：頂点同型の像と端点の等式による移送の整合性。
方針：ホモトピー圏の関手性を同型の像へ移す。
規約：端点を厳密に指定し等式による同定を明示する。
使われ方：表現の cartesian 制限と図式の前合成の比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：頂点同型を二つの射で続けて写す作用は合成射で写す作用。
方針：ホモトピー圏の関手の合成則を使う。
規約：単体集合の充填条件を要求しない。
使われ方：可換四角形の両経路の比較。 -/
lemma vertexIso_map_comp {X Y Z : SSet.{u}} {x y : X _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) (f : X ⟶ Y) (g : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e f) g = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (f ≫ g) := by
  apply Iso.ext
  have h := Functor.congr_hom congr($(hoFunctor.map_comp f g).toFunctor) e.hom
  simpa [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map] using h.symm

/-- 概要：頂点同型の合成は同型の像の合成へ写る。
方針：ホモトピー圏の関手による同型の像の合成則を使う。
規約：三頂点の順序を保つ。
使われ方：端点の同定を含む比較を整理する。 -/
lemma vertexIso_map_trans {X Y : SSet.{u}} {x y z : X _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso y z) (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (e ≪≫ d) f = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e f ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map d f :=
  (hoFunctor.map f).toFunctor.mapIso_trans e d

/-- 概要：逆同型の像は像の逆同型。
方針：同型の像の定義を使う。
規約：逆を取る際に別の同型を選ばない。
使われ方：端点の等式による比較を整理する。 -/
lemma vertexIso_map_symm {X Y : SSet.{u}} {x y : X _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e.symm f = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e f).symm := rfl

/-- 概要：等しい射による頂点同型の像は端点の同定を介して一致する。
方針：射の等式を消去し恒等の移送へ戻す。
規約：始点と終点の両方の等式を明示する。
使われ方：図式射影の可換式から比較の自然性を得る。 -/
lemma vertexIso_map_congr {X Y : SSet.{u}} {x y : X _⦋0⦌}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) (f g : X ⟶ Y) (h : f = g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e f =
      eqToIso (congrArg SSet.HomotopyCategory.mk
        (congrArg (fun k : X ⟶ Y ↦ k.app _ x) h)) ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e g ≪≫
      (eqToIso (congrArg SSet.HomotopyCategory.mk
        (congrArg (fun k : X ⟶ Y ↦ k.app _ y) h))).symm := by
  subst g
  simp

/-- 概要：端点の等式で作った同型の像は写した端点の等式の同型。
方針：等式を消去して恒等射の像を計算する。
規約：頂点の等式による移送を新たな選択に置き換えない。
使われ方：表現の頂点公式を写した後の端点の整理。 -/
lemma vertexIso_map_eqToIso {X Y : SSet.{u}} {x y : X _⦋0⦌}
    (h : x = y) (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (eqToIso (congrArg SSet.HomotopyCategory.mk h)) f =
      eqToIso (congrArg SSet.HomotopyCategory.mk (congrArg (fun z ↦ f.app _ z) h)) := by
  subst y
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
