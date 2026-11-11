module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PointCosliceEdge
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration

/-!
概要：始点を固定した cocartesian な辺の coslice の全部分複体。
方針：点の coslice の頂点から cocartesian な辺を選ぶ。
規約：高次単体は選ばれた頂点の全部分複体。
使われ方：Kerodon §5.1.1（Tag 01T4）・5.1.4（Tag 01U9） の輸送の選択の可縮性。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：辺の一次単体が同じなら cocartesian 性は同値。
方針：外側ホーンの指定する辺の等式だけを置換する。
規約：端点の等式の証明や端点の表示は問わない。
使われ方：Kerodon §5.1.1（Tag 01T4） の辺の表示の変更。 -/
lemma hasCocartesianHornLifting_congr {E B : SSet.{u}} (p : E ⟶ B)
    {x y x' y' : E _⦋0⦌}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj E) x' y'} (h : e.edge = f.edge) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p e ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p f := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting
  rw [h]

/-- 概要：点の coslice の頂点が cocartesian な辺を表す条件。
方針：標準区間への表示を使う。
規約：始点は射 a で指定する。
使われ方：Kerodon §5.1.1（Tag 01T4） の cocartesian な対象の選択。 -/
def IsCocartesianCosliceVertex {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E)
    (p : E ⟶ B) (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting p (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge a σ)

/-- 概要：始点を固定した cocartesian な辺からなる coslice の全部分複体。
方針：cocartesian な辺を表す頂点が張る全部分複体を取る。
規約：高次単体の追加条件は全頂点の条件のみ。
使われ方：Kerodon §5.1.4（Tag 01U9） の輸送の選択の圏。 -/
def cocartesianCoslice {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) (IsCocartesianCosliceVertex a p) : SSet.{u})

/-- 概要：cocartesian な coslice の元の coslice への包含。
方針：全部分複体の包含を使う。
規約：全次数で単射。
使われ方：Kerodon §5.1.4（Tag 01U9） の輸送の像の計算。 -/
def cocartesianCosliceι {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) :
    cocartesianCoslice a p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (IsCocartesianCosliceVertex a p)).ι

/-- 概要：cocartesian な coslice は元が quasicategory なら quasicategory。
方針：coslice の全部分複体の quasicategory 性を使う。
規約：標的 B や p のファイブレーション性は不要。
使われ方：Kerodon §5.1.4（Tag 01U9） の輸送の選択の圏構造。 -/
instance cocartesianCoslice_quasicategory {E B : SSet.{u}} [Quasicategory E]
    (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) : Quasicategory (cocartesianCoslice a p) := by
  unfold cocartesianCoslice
  infer_instance

/-- 概要：cocartesian な coslice から基底の点の coslice への射。
方針：全部分複体から含めて元の射で後合成する。
規約：基底の点は a≫p で指定する。
使われ方：Kerodon §5.1.4（Tag 01U9） の基底の辺から輸送への比較。 -/
def cocartesianCosliceProjection {E B : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ E) (p : E ⟶ B) :
    cocartesianCoslice a p ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (a ≫ p) :=
  cocartesianCosliceι a p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
