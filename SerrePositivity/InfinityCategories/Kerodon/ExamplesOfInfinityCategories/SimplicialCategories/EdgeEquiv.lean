module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ArrowData

/-!
概要：coherent nerve の端点を指定した辺と通常の射の同値。
方針：一単体の射データを取り出し、面の等式で二端点を合わせる。
規約：端点は coherentNerveVertex で表す。局所 Kan 性は不要。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、pointed-space fiber の頂点と Kan 複体の点の対応。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：coherent な辺の射データの始点は指定した対象。
方針：始点の面の等式を零単体の対象で評価する。
規約：辺の始点は coherentNerveVertex X。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、復元した通常の射の始域の調整。 -/
lemma coherentNerveEdge_source {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (e : (SimplicialNerve C).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e.edge).1 = X :=
  congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject e.src_eq

/-- 概要：coherent な辺の射データの終点は指定した対象。
方針：終点の面の等式を零単体の対象で評価する。
規約：辺の終点は coherentNerveVertex Y。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、復元した通常の射の終域の調整。 -/
lemma coherentNerveEdge_target {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (e : (SimplicialNerve C).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e.edge).2.1 = Y :=
  congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject e.tgt_eq

/-- 概要：coherent nerve の辺から端点を固定した通常の射を復元する。
方針：抽出した射の両側に端点の等号に沿う射を合成する。
規約：向きは始点 X から終点 Y。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、pointed space の点の復元。 -/
noncomputable def coherentNerveEdgeToHom {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C}
    (e : (SimplicialNerve C).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)) : X ⟶ Y :=
  eqToHom (coherentNerveEdge_source e).symm ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e.edge).2.2 ≫
    eqToHom (coherentNerveEdge_target e)

/-- 概要：通常の射から作った辺を戻すと元の射になる。
方針：端点の等号の射を恒等にし、射データの計算を使う。
規約：等号の証明の選択に依存しない。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、辺の表示の単射性。 -/
lemma coherentNerveEdgeToHom_edge {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (f : X ⟶ Y) : coherentNerveEdgeToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f) = f := by
  change eqToHom (show X = X from rfl) ≫
    (SimplicialCategory.homEquiv' X Y).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' X Y f) 0) ≫
        eqToHom (show Y = Y from rfl) = f
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, Equiv.symm_apply_apply]

/-- 概要：射の端点を等号に沿って移しても端点付き射データは同じ。
方針：依存和を分解して二つの等号を消去する。
規約：二端点の移送は始域側で逆向き、終域側で順向き。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、coherent な辺の復元時の端点の調整。 -/
lemma arrowData_transport {C : Type v} [Category.{u} C] {X Y : C}
    (a : Σ A B : C, A ⟶ B) (hX : a.1 = X) (hY : a.2.1 = Y) :
    (⟨X, Y, eqToHom hX.symm ≫ a.2.2 ≫ eqToHom hY⟩ : Σ A B : C, A ⟶ B) = a := by
  rcases a with ⟨A, B, f⟩
  dsimp at hX hY
  subst X
  subst Y
  simp

/-- 概要：辺から復元した通常の射は元の辺を与える。
方針：端点の等式で対象を置き換え、一単体の射データの同値で比較する。
規約：辺の構造の等号は一単体の等号に帰着する。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、辺の表示の全射性。 -/
lemma coherentNerveEdge_hom {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} (e : (SimplicialNerve C).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (coherentNerveEdgeToHom e) = e := by
  apply SSet.Edge.ext
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowDataEquiv C).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (coherentNerveEdgeToHom e)).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_edge, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_of_arrow]
  change (⟨X, Y, eqToHom (coherentNerveEdge_source e).symm ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e.edge).2.2 ≫ eqToHom (coherentNerveEdge_target e)⟩ :
      Σ A B : C, A ⟶ B) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData e.edge
  exact arrowData_transport _ (coherentNerveEdge_source e) (coherentNerveEdge_target e)

/-- 概要：coherent nerve の二対象間の辺と通常の射は同値。
方針：通常の射の coherent 表示と端点を合わせた復元を互いに逆にする。
規約：写像空間の高次単体の比較は別に扱う。
使われ方：Kerodon Remark 3.1.6.3（Tag 01YZ）、𝒮 の辺と Kan 複体間の写像の対応。 -/
noncomputable def coherentNerveEdgeEquiv {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) :
    (SimplicialNerve C).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) ≃ (X ⟶ Y) where
  toFun := coherentNerveEdgeToHom
  invFun := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
  left_inv := coherentNerveEdge_hom
  right_inv := coherentNerveEdgeToHom_edge

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
