module
public import SerrePositivity.KST.Fibration.WeakStringsStability
public import SerrePositivity.KST.SConstruction.SClosedPredicates
public import SerrePositivity.KST.LocalizingInvariants.StableCofiberWide

/-!
概要：閉じた安定部分圏 P に cofiber を持つ辺の全有限旗を商なしで構成する。
方針：完全な cofiber 評価による P の逆像を全辺で交差し、元の辺条件と照合する。
規約：入力は B と P のみ。retract 閉包・商関手・完備化を使わない。
使われ方：K-B2-S1 の相対旗と K-cof 向け fiber の共通供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration.Relative

/-- 概要：同じ B の K-B 図式 API 用の包装。方針：既存構造を使う。
規約：底は厳密に同じ。使われ方：完全な cofiber 評価。 -/
def flagAmbient (B : StableModel.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u} :=
  ⟨B.carrier, inferInstance, inferInstance⟩

/-- 概要：P は指定安定閉包と一致する。方針：閉包の生成子で帰納する。
規約：retract 閉包を使わない。使われ方：全 W 辺の二対三性の消費。 -/
lemma closedStableClosure_iff {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (x : B.carrier _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure {x | P.predicate x} x ↔ P.predicate x := by
  constructor
  · intro h
    induction h with
    | of_mem hx => exact hx
    | of_zero hx => exact P.zero_mem hx
    | of_iso e _ ih => exact P.of_iso ih e
    | of_cofiber t ht _ _ ih₀ ih₁ =>
      exact P.pushout_mem t.square ht ih₀ ih₁ (P.zero_mem t.zero_corner)
    | of_fiber t ht _ _ ih₁ ih₂ =>
      exact P.pullback_mem t.square ht ih₁ (P.zero_mem t.zero_corner) ih₂
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem

/-- 概要：元の P に cofiber を持つ辺。方針：既存の実 cofiber 辺条件。
規約：商の反転辺で代用しない。使われ方：全旗の所属条件。 -/
def closedStableEdges {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    Set (B.carrier _⦋1⦌) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges {x | P.predicate x}

/-- 概要：元の全 W 単体の wide 部分複体。方針：全辺条件。
規約：P 自身を使用。使われ方：旗全体の因子分解。 -/
def closedStableWide {B : StableModel.{u}} (P : ClosedStablePredicate B) : B.carrier.Subcomplex :=
  edgewiseSubcomplex (closedStableEdges P)

/-- 概要：同じ wide 部分複体を既存の安定閉包版へ照合。
方針：P の安定閉性。規約：retract 閉包なし。使われ方：内ホーンの全持ち上げ。 -/
lemma closedStableWide_eq {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    closedStableWide P = stableCofiberWide {x | P.predicate x} := by
  unfold closedStableWide closedStableEdges stableCofiberWide
  rw [show {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure {x | P.predicate x} x} = {x | P.predicate x} from
    Set.ext (closedStableClosure_iff P)]

/-- 概要：元の W 包含は inner fibration。方針：安定閉包版の公開定理。
規約：商なし。使われ方：旗の貼り合わせの反映。 -/
instance closedStableWide_innerFibration {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    InnerFibration (closedStableWide P).ι := by
  rw [closedStableWide_eq]
  infer_instance

/-- 概要：同じ実 cofiber による W 所属判定。方針：安定閉包を P に戻す。
規約：cofiber の選択に依存しない。使われ方：相対 cofiber 射影の制限。 -/
lemma closedStableEdges_iff_cofiber {B : StableModel.{u}} (P : ClosedStablePredicate B)
    {x y : B.carrier _⦋0⦌}
    {f : Truncated.Edge (X := (truncation 2).obj B.carrier) x y} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.CofiberSquare f) :
    f.edge ∈ closedStableEdges P ↔ P.predicate s.cofiber := by
  have he : {x | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure {x | P.predicate x} x} = {x | P.predicate x} :=
    Set.ext (closedStableClosure_iff P)
  unfold closedStableEdges
  rw [← he, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_edge_mem_iff, closedStableClosure_iff]

/-- 概要：元の cofiber 評価の P 逆像。方針：完全関手で閉条件を引き戻す。
規約：全矢印図式圏上の条件。使われ方：旗圏の安定性。 -/
def closedArrowPredicate {B : StableModel.{u}} (P : ClosedStablePredicate B) :
    ClosedStablePredicate (ambientDiagramModel (Δ[1] : SSet.{u}) (flagAmbient B)) :=
  P.comap (arrowCofiberMap (flagAmbient B))

/-- 概要：完全な cofiber 評価と元の辺条件の照合。方針：同じ切断の底辺を回収。
規約：元の全 cofiber 図式を保持。使われ方：全旗の頂点条件。 -/
lemma closedArrowPredicate_iff {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (v : ((ihom (Δ[1] : SSet.{u})).obj B.carrier) _⦋0⦌) :
    (closedArrowPredicate P).predicate v ↔ arrowVertexSimplex v ∈ closedStableEdges P := by
  let w := (arrowCofiberSection (flagAmbient B)).app (Opposite.op ⦋0⦌) v
  have hw := ConcreteCategory.congr_hom
    (NatTrans.congr_app (arrowCofiberSection_projection (flagAmbient B))
      (Opposite.op ⦋0⦌)) v
  have he : (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram w.val)).edge = arrowVertexSimplex v := by
    rw [← cofiberProjection_vertex_simplex]
    exact congrArg arrowVertexSimplex hw
  have hc := cofiberVertex_corner (flagAmbient B) w
    (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1)
  change (arrowCofiberMap (flagAmbient B)).val.app (Opposite.op ⦋0⦌) v =
    (vertexCofiberSquare w).cofiber at hc
  change P.predicate ((arrowCofiberMap (flagAmbient B)).val.app _ v) ↔ _
  rw [hc, ← closedStableEdges_iff_cofiber P (vertexCofiberSquare w), he]

/-- 概要：全辺が W に属する元の旗の条件。方針：wide 部分複体への全体持ち上げ。
規約：隣接辺だけに制限しない。使われ方：仕様の R_P の対象。 -/
def closedFlagPredicate {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory)
    (v : ((ihom (stdSimplex.obj n)).obj B.carrier) _⦋0⦌) : Prop :=
  simplexVertexValue n v ∈ (edgewiseSubcomplex (closedStableEdges P)).obj (Opposite.op n)

/-- 概要：全辺の完全な評価で交差した閉じた安定条件。
方針：既存の iInter・comap を合成。規約：商なし。使われ方：R_P の安定模型。 -/
def closedFlagStablePredicate {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory) :
    ClosedStablePredicate (ambientDiagramModel (stdSimplex.obj n) (flagAmbient B)) :=
  ClosedStablePredicate.iInter (fun α : ⦋1⦌ ⟶ n =>
    (closedArrowPredicate P).comap (diagramRestrictionMap (flagAmbient B) α))

/-- 概要：全体として W 内に持ち上がることと閉じた条件の一致。
方針：各辺で同じ cofiber 判定を使う。規約：全次元。使われ方：元の全部分旗の回収。 -/
lemma closedFlagStablePredicate_iff {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory)
    (v : ((ihom (stdSimplex.obj n)).obj B.carrier) _⦋0⦌) :
    (closedFlagStablePredicate P n).predicate v ↔ closedFlagPredicate P n v := by
  change (∀ α : ⦋1⦌ ⟶ n, (closedArrowPredicate P).predicate
    (((pre (stdSimplex.map α)).app B.carrier).app (Opposite.op ⦋0⦌) v)) ↔ _
  unfold closedFlagPredicate edgewiseSubcomplex
  apply forall_congr'
  intro α
  rw [closedArrowPredicate_iff]
  exact (congrArg (· ∈ closedStableEdges P) (simplexVertexValue_reindex α v)).to_iff

/-- 概要：仕様の全有限 W 旗の安定模型。方針：同じ閉条件の全部分圏。
規約：全自然変換を含む。使われ方：F と定数旗の実現。 -/
def closedFlagModel {B : StableModel.{u}} (P : ClosedStablePredicate B)
    (n : SimplexCategory) : StableModel.{u} := closedStableModel (closedFlagStablePredicate P n)

end SerrePositivity.KST.Fibration.Relative
