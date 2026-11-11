module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCut
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentMapNaturality

/-!
# 語の単調写像による zigzag の列の圧縮

概要：色を保つ単調写像の各 fiber の元の列を合成し、空 fiber では恒等列を挿入。
方針：切断位置を新しい頂点に使い、同方向区間の合成を新しい列に使う。
規約：元の始点と終点・全縦射・弱同値の条件を保持する。
使われ方：全語で添字付ける hammock 図式の各遷移。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

/-- 元の向きに応じた列の始点。 -/
def source {I : Type*} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : I) : I :=
  match d with | .forward => p | .backward => q

/-- 元の向きに応じた列の終点。 -/
def target {I : Type*} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : I) : I :=
  match d with | .forward => q | .backward => p

/-- 向きに応じた圏の射を、元の二頂点の実際の向きの射へ戻す。 -/
def columnAux {I : Type*} (V : I → C) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (V p) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (V q)) →
      (V (source d p q) ⟶
        V (target d p q)) :=
  match d with
  | .forward => fun m => m
  | .backward => fun m => m.unop

/-- 元の同方向の fiber を一つの列に合成する。 -/
def column (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (j : Fin b.length) :
    S.vertex (f.cut (b.source j)) ⟶ S.vertex (f.cut (b.target j)) :=
  columnAux (fun k => S.vertex (f.cut k)) (b.direction j) j.castSucc j.succ
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map (b.direction j) S (f.cut j.castSucc) (f.cut j.succ)
      (f.cut_monotone (Fin.castSucc_le_succ j))
      (fun i hi hi' => f.fiber_direction j i hi hi'))

/-- 後ろ向きの射の許容条件を、元の圏へ戻す。 -/
lemma columnAux_mem {I : Type*} (V : I → C) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : I)
    (m : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (V p) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (V q))
    (hd : d = .backward) (hm : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.allowed d W m) : W (columnAux V d p q m) := by
  subst d
  exact hm

/-- 後ろ向きの fiber の合成は元の弱同値。 -/
lemma column_mem [W.IsMultiplicative] (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y)
    (j : Fin b.length) (hj : b.direction j = .backward) : W (column f S j) :=
  columnAux_mem _ _ _ _ _ hj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map_allowed _ _ _ _ _ _)

/-- 列を圧縮した zigzag の実際の全頂点・全列。 -/
def obj [W.IsMultiplicative] (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b X Y where
  vertex j := S.vertex (f.cut j)
  first := (congrArg S.vertex (f.cut_zero)).trans S.first
  last := (congrArg S.vertex (f.cut_last)).trans S.last
  arrow := column f S
  backward_mem := column_mem f S

/-- 向きに応じた射の正方形を元の圏の式で表す。 -/
def square {P Q P' Q' : C} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d Q) →
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d P' ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d Q') → (P ⟶ P') → (Q ⟶ Q') → Prop :=
  match d with
  | .forward => fun m n fp fq => m ≫ fq = fp ≫ n
  | .backward => fun m n fp fq => m.unop ≫ fp = fq ≫ n.unop

/-- 区間合成の自然性を向きに応じた一つの正方形にまとめる。 -/
lemma segment_square (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T)
    (p q : Fin (a.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d) :
    square d (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S p q hpq hd) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d T p q hpq hd) (g.app p) (g.app q) := by
  cases d
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentMapNaturality.forward_map_comm g p q hpq hd
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentMapNaturality.backward_map_comm g p q hpq hd

/-- 向きに応じた正方形から、元の二頂点の列の正方形を回収する。 -/
lemma columnAux_comm {I : Type*} (V U : I → C) (η : ∀ i, V i ⟶ U i)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (p q : I)
    (m : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (V p) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (V q))
    (n : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (U p) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (U q))
    (h : square d m n (η p) (η q)) :
    columnAux V d p q m ≫ η (target d p q) =
      η (source d p q) ≫ columnAux U d p q n := by
  cases d
  · exact h
  · exact h

/-- 列の合成は元の両端の縦射の正方形と可換。 -/
lemma column_comm (f : a ⟶ b) {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T)
    (j : Fin b.length) :
    column f S j ≫ g.app (f.cut (b.target j)) =
      g.app (f.cut (b.source j)) ≫ column f T j :=
  columnAux_comm (fun k => S.vertex (f.cut k)) (fun k => T.vertex (f.cut k))
    (fun k => g.app (f.cut k)) _ _ _ _ _ (segment_square _ g _ _ _ _)

/-- 指定端点の元の恒等条件を、頂点の等式に沿って移す。 -/
lemma fixed_app {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T)
    {i j : Fin (a.length + 1)} (h : i = j) {Z : C}
    (hS : S.vertex j = Z) (hT : T.vertex j = Z)
    (hg : g.app j = eqToHom (hS.trans hT.symm)) :
    g.app i = eqToHom (((congrArg S.vertex h).trans hS).trans
      ((congrArg T.vertex h).trans hT).symm) := by
  cases h
  exact hg

/-- 元の切断位置の全縦弱同値を保持する。 -/
def map [W.IsMultiplicative] (f : a ⟶ b) {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y} (g : S ⟶ T) :
    obj f S ⟶ obj f T where
  app j := g.app (f.cut j)
  app_mem _j := g.app_mem _
  first := fixed_app g f.cut_zero S.first T.first g.first
  last := fixed_app g f.cut_last S.last T.last g.last
  comm := column_comm f g

/-- 任意の色を保つ単調写像による、元の zigzag 圏間の遷移関手。 -/
def functor [W.IsMultiplicative] (f : a ⟶ b) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W b X Y where
  obj := obj f
  map := map f
  map_id _ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (fun _ => rfl)
  map_comp _ _ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (fun _ => rfl)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction
