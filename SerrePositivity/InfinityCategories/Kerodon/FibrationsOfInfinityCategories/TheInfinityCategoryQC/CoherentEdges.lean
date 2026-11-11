module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.ArrowData
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoherentVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：単体的圏の射を coherent nerve の辺へ送り、指定射と両端点を回収する。
方針：二点順序圏の通常の図式を豊穣化し、順方向の Hom の零単体で評価する。
規約：任意の native な辺からの読み戻しも定義し、追加の Kan 仮定を用いない。
使われ方：Cat_∞ の辺を小さい quasicategory 間の関手として表示する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe v u
open CategoryTheory MonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]

/-- 概要：通常の射を coherent nerve の辺として表示する。
方針：ULift した二点順序圏上の一本の矢印を豊穣関手にする。
規約：ULift の対象・Hom の宇宙の違いを明示した順序圏の関手を用いる。
使われ方：Cat_∞ 内の図式の辺の構成。 -/
def coherentEdge {X Y : C} (f : X ⟶ Y) : (SimplicialNerve C) _⦋1⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge

/-- 概要：coherent nerve の任意の辺から元の単体的圏の射を取り出す。
方針：端点 0 から 1 の標準 Path で Hom 写像を評価し、豊穣零単体の対応を使う。
規約：始域と終域は元の辺の対象成分そのもの。
使われ方：Cat_∞ の指定辺から実際の関手を読み戻す。 -/
def coherentEdgeHom (F : (SimplicialNerve C) _⦋1⦌) :
    F.obj ⟨ULift.up 0⟩ ⟶ F.obj ⟨ULift.up 1⟩ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData F).2.2

/-- 概要：指定射から作った辺の読み戻しは元の射に等しい。
方針：豊穣零単体との全単射で比較し、定値 Hom の定義を展開する。
規約：元の射を同型やホモトピーで置き換えず厳密に回収する。
使われ方：Cat_∞ に構成した辺が指定関手を表すことの検証。 -/
lemma coherentEdgeHom_edge {X Y : C} (f : X ⟶ Y) :
    coherentEdgeHom (coherentEdge f) = f := by
  change (SimplicialCategory.homEquiv' X Y).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (SimplicialCategory.homEquiv' X Y f) 0) = f
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero, Equiv.symm_apply_apply]

/-- 概要：指定射の coherent な辺の始点は元の始域の頂点。
方針：頂点を対象へ読み戻す全単射で比較する。
規約：δ₁ は始点を取り出す。
使われ方：Cat_∞ の辺の始域の厳密な表示。 -/
lemma coherentEdge_source {X Y : C} (f : X ⟶ Y) :
    (SimplicialNerve C).δ 1 (coherentEdge f) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex X := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertexEquiv.symm.injective
  rfl

/-- 概要：指定射の coherent な辺の終点は元の終域の頂点。
方針：頂点を対象へ読み戻す全単射で比較する。
規約：δ₀ は終点を取り出す。
使われ方：Cat_∞ の辺の終域の厳密な表示。 -/
lemma coherentEdge_target {X Y : C} (f : X ⟶ Y) :
    (SimplicialNerve C).δ 0 (coherentEdge f) = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertexEquiv.symm.injective
  rfl

/-- 概要：任意の coherent な辺は読み戻した射から厳密に復元できる。
方針：F1 の全単体の射データの復元定理をそのまま適用する。
規約：同型やホモトピーによる比較に弱めず、native な辺の等式を返す。
使われ方：Cat_∞ の任意の辺を実際の関手へ還元する。 -/
lemma coherentEdge_recover (F : (SimplicialNerve C) _⦋1⦌) :
    coherentEdge (coherentEdgeHom F) = F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveArrowData_reconstruct F

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
