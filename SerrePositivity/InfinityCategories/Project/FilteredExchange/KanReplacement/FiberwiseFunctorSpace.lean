module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInternalHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConstantDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram

/-!
概要：底の図式を各パラメータで定値に固定した、fiber ごとの関手の全空間。
方針：内部 Hom の底射を定値図式関手で引き戻す。
規約：同じ底の頂点を共有する射だけを収める。
使われ方：一般 coherent な図式の fiber ごとの path 模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：底の頂点を共有する K 上の図式の全空間。
方針：全関手空間を底の定値図式に沿って引き戻す。
規約：K の有限性は定義に不要。使われ方：fiber ごとの path 空間の全空間。 -/
def fiberwiseFunctorSpace {E B : SSet.{u}} (p : E ⟶ B) (K : SSet.{u}) : SSet.{u} :=
  pullback ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B)

/-- 概要：fiber ごとの関手の共有する底の頂点への射影。
方針：引き戻しの第二射影。
規約：底を変更しない。使われ方：再び left fibration として扱う。 -/
def fiberwiseFunctorProjection {E B : SSet.{u}} (p : E ⟶ B) (K : SSet.{u}) :
    fiberwiseFunctorSpace p K ⟶ B :=
  pullback.snd ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B)

/-- 概要：fiber ごとの関手の全空間は同じ底上の left fibration。
方針：内部 Hom の left fibration 性を定値図式で底変換する。
規約：底の充填性は不要。使われ方：一般 coherent 図式の新しい値の模型。 -/
instance fiberwiseFunctorProjection_leftFibration {E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (fiberwiseFunctorProjection p K) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := (ihom K).map p))⟩

/-- 概要：fiber ごとの関手の評価の底は、共有する底の頂点の射影。
方針：引き戻しの可換式を uncurry する。
規約：全パラメータで底を固定。使われ方：指定された path の底の検査。 -/
lemma fiberwiseFunctorUncurry_projection {E B : SSet.{u}} (p : E ⟶ B) (K : SSet.{u}) :
    uncurry (pullback.fst ((ihom K).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram K B)) ≫ p =
      snd K (fiberwiseFunctorSpace p K) ≫ fiberwiseFunctorProjection p K := by
  rw [← uncurry_natural_right, pullback.condition, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.uncurry_comp_constantDiagram]
  rfl

/-- 概要：fiber ごとの path の指定端点の全空間への評価。
方針：path 座標を指定端点で評価する。
規約：0 が始点、1 が終点。使われ方：元の二射を保つ path 引き戻し。 -/
def fiberwiseIntervalEndpoint {E B : SSet.{u}} (p : E ⟶ B) (e : Fin 2) :
    fiberwiseFunctorSpace p (Δ[1] : SSet.{u}) ⟶ E :=
  pullback.fst ((ihom (Δ[1] : SSet.{u})).map p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram Δ[1] B) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans e).app E

/-- 概要：path の両端評価は共有する元の底射に重なる。
方針：評価の自然性と定値図式の評価を使う。
規約：両端で厳密に一致。使われ方：fiber ごとの二入力の整合条件。 -/
lemma fiberwiseIntervalEndpoint_projection {E B : SSet.{u}} (p : E ⟶ B) (e : Fin 2) :
    fiberwiseIntervalEndpoint p e ≫ p = fiberwiseFunctorProjection p Δ[1] := by
  have hn : (ihom (Δ[1] : SSet.{u})).map p ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans e).app B =
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans e).app E ≫ p := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans e).naturality p
  rw [fiberwiseIntervalEndpoint, Category.assoc, ← hn,
    ← Category.assoc, pullback.condition, Category.assoc]
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.constantDiagram (Δ[1] : SSet.{u}) B ≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans e).app B = 𝟙 B := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    change B.map (𝟙 n) x = x
    exact B.map_id_apply n x
  rw [h, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
