module

public import SerrePositivity.InfinityCategories.F2.CoherentOrderDiagram

/-!
概要：単体的圏の射を coherent nerve の辺へ送り、指定射と両端点を回収する。
方針：二点順序圏の通常の図式を豊穣化し、順方向の Hom の零単体で評価する。
規約：任意の native な辺からの読み戻しも定義し、追加の Kan 仮定を用いない。
使われ方：Cat_∞ の辺を小さい quasicategory 間の関手として表示する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe v u
open CategoryTheory MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 概要：通常の射を coherent nerve の辺として表示する。
方針：ULift した二点順序圏上の一本の矢印を豊穣関手にする。
規約：ULift の対象・Hom の宇宙の違いを明示した順序圏の関手を用いる。
使われ方：Cat_∞ 内の図式の辺の構成。 -/
def coherentEdge {X Y : C} (f : X ⟶ Y) : (SimplicialNerve C) _⦋1⦌ :=
  coherentOrderDiagram ((show ULift.{v} (Fin 2) ⥤ Fin 2 from
    { obj := ULift.down
      map {a b} g := homOfLE
        (show a.down ≤ b.down from @leOfHom (ULift.{v} (Fin 2)) _ a b g) }) ⋙
          ComposableArrows.mk₁ f)

/-- 概要：coherent nerve の任意の辺から元の単体的圏の射を取り出す。
方針：端点 0 から 1 の標準 Path で Hom 写像を評価し、豊穣零単体の対応を使う。
規約：始域と終域は元の辺の対象成分そのもの。
使われ方：Cat_∞ の指定辺から実際の関手を読み戻す。 -/
def coherentEdgeHom (F : (SimplicialNerve C) _⦋1⦌) :
    F.obj ⟨ULift.up 0⟩ ⟶ F.obj ⟨ULift.up 1⟩ :=
  (SimplicialCategory.homEquiv' _ _).symm
    ((F.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩).app _
      (nerveEquiv.symm (Coherent.pathOfInterior
        (show ULift.up.{v} (0 : Fin 2) < ULift.up 1 by decide) ∅)))

/-- 概要：指定射から作った辺の読み戻しは元の射に等しい。
方針：豊穣零単体との全単射で比較し、定値 Hom の定義を展開する。
規約：元の射を同型やホモトピーで置き換えず厳密に回収する。
使われ方：Cat_∞ に構成した辺が指定関手を表すことの検証。 -/
lemma coherentEdgeHom_edge {X Y : C} (f : X ⟶ Y) :
    coherentEdgeHom (coherentEdge f) = f := by
  apply (SimplicialCategory.homEquiv' X Y).injective
  unfold coherentEdgeHom
  change (SimplicialCategory.homEquiv' X Y)
    ((SimplicialCategory.homEquiv' X Y).symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- 概要：指定射の coherent な辺の始点は元の始域の頂点。
方針：頂点を対象へ読み戻す全単射で比較する。
規約：δ₁ は始点を取り出す。
使われ方：Cat_∞ の辺の始域の厳密な表示。 -/
lemma coherentEdge_source {X Y : C} (f : X ⟶ Y) :
    (SimplicialNerve C).δ 1 (coherentEdge f) = coherentVertex X := by
  apply coherentVertexEquiv.symm.injective
  rfl

/-- 概要：指定射の coherent な辺の終点は元の終域の頂点。
方針：頂点を対象へ読み戻す全単射で比較する。
規約：δ₀ は終点を取り出す。
使われ方：Cat_∞ の辺の終域の厳密な表示。 -/
lemma coherentEdge_target {X Y : C} (f : X ⟶ Y) :
    (SimplicialNerve C).δ 0 (coherentEdge f) = coherentVertex Y := by
  apply coherentVertexEquiv.symm.injective
  rfl

end SerrePositivity.InfinityCategories.F2
