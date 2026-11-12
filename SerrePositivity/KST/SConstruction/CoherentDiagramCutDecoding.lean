module
public import SerrePositivity.KST.SConstruction.CoherentPathMappingHomotopy

/-! # Coherent 図式の高次単体の全 Path 円柱の復号
概要：図式の各高次単体から、元の豊穣 Hom 内の全 Path の実合成円柱を取り出す。
方針：元の単体の豊穣作用と切断点挿入を用い、全単体作用との可換性を証明する。
規約：パラメータ単体集合と豊穣 Hom の宇宙を分け、局所 Kan 性は仮定しない。
使われ方：元の K prism の各高次単体に境界固定の実円柱を供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {A : SSet.{max u v}}

/-- 元の図式の単体の全 Path を評価する、元の豊穣 Hom に値を取る族。 -/
def coherentDiagramPathFamily (Q : A ⟶ SimplicialNerve C) {n : ℕ} (p : A _⦋n⦌)
    (i k : Fin (n + 1)) :
    nerve (Path (ULift.up i : ULift.{u} _) (ULift.up k)) ⟶
      SimplicialCategory.sHom ((Q.app _ p).obj (.mk (ULift.up i)))
        ((Q.app _ p).obj (.mk (ULift.up k))) :=
  (Q.app _ p).map (.mk (ULift.up i)) (.mk (ULift.up k))

/-- 元の図式の高次単体から復号した、全 Path を動かす実合成円柱。 -/
def coherentDiagramCutHomotopy (Q : A ⟶ SimplicialNerve C) {n : ℕ} (p : A _⦋n⦌)
    (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    SSet.Homotopy (coherentDiagramPathFamily Q p i k)
      (coherentPathCutSplit (show (ULift.up i : ULift.{u} _) ≤ ULift.up j from hij)
          (show (ULift.up j : ULift.{u} _) ≤ ULift.up k from hjk) ≫
        (coherentDiagramPathFamily Q p i j ⊗ₘ coherentDiagramPathFamily Q p j k) ≫
          eComp SSet ((Q.app _ p).obj (.mk (ULift.up i)))
            ((Q.app _ p).obj (.mk (ULift.up j))) ((Q.app _ p).obj (.mk (ULift.up k)))) :=
  coherentPathMappingCutHomotopy (Q.app _ p) hij hjk

/-- 合成面の全高次単体は、元の図式から復号した実円柱で全時刻にわたり固定。 -/
lemma coherentDiagramCutHomotopy_relative (Q : A ⟶ SimplicialNerve C) {n : ℕ}
    (p : A _⦋n⦌) (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := (ULift.up i : ULift.{u} _)) (c := ULift.up k)
        (ULift.up j)).ι ▷ (Δ[1] : SSet.{u})) ≫
        (coherentDiagramCutHomotopy Q p i j k hij hjk).h =
      CartesianMonoidalCategory.fst
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := (ULift.up i : ULift.{u} _)) (c := ULift.up k)
          (ULift.up j) : SSet.{u}) Δ[1] ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up j)).ι ≫ coherentDiagramPathFamily Q p i k :=
  coherentPathMappingCutHomotopy_relative (Q.app _ p) hij hjk

/-- 端点 Path 上の辺は元の単体の同じ合成三角形の辺を厳密に回収する。 -/
lemma coherentDiagramCutHomotopy_endpoint_edge (Q : A ⟶ SimplicialNerve C) {n : ℕ}
    (p : A _⦋n⦌) (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (coherentDiagramCutHomotopy Q p i j k hij hjk)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (coherentEndpointPath
        (show (ULift.up i : ULift.{u} _) ≤ ULift.up k from hij.trans hjk)))).edge =
      (coherentSimplexCompositionEdge (Q.app _ p) i j k hij hjk).edge :=
  coherentPathMappingCutHomotopy_endpoint_edge (Q.app _ p) hij hjk

/-- 面・退化を含む全単体作用で同じ円柱を制限する。対象の表示は依存等号で照合する。 -/
lemma coherentDiagramCutHomotopy_naturality (Q : A ⟶ SimplicialNerve C) {m n : ℕ}
    (p : A _⦋n⦌) (θ : ⦋m⦌ ⟶ ⦋n⦌) (i j k : Fin (m + 1))
    (hij : i ≤ j) (hjk : j ≤ k) :
    HEq (coherentDiagramCutHomotopy Q (A.map θ.op p) i j k hij hjk).h
      ((nerveMap (SimplicialThickening.functorMap θ.toOrderHom.uliftMap
        (.mk (ULift.up i)) (.mk (ULift.up k))) ▷ (Δ[1] : SSet.{u})) ≫
        (coherentDiagramCutHomotopy Q p (θ.toOrderHom i) (θ.toOrderHom j)
          (θ.toOrderHom k) (θ.toOrderHom.monotone hij) (θ.toOrderHom.monotone hjk)).h) := by
  exact (coherentPathMappingCutHomotopy_heq
    (NatTrans.naturality_apply Q θ.op p) hij hjk).trans
    (heq_of_eq (coherentPathMappingCutHomotopy_reindex (Q.app _ p)
      θ.toOrderHom.uliftMap hij hjk))

end SerrePositivity.KST.SConstruction
