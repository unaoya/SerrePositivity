module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanIntervalPullbackNative
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpecifiedConeTransportRestrictions
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.HomotopyVerticalRestriction

/-!
概要：元の Kan cospan の path 引き戻し錐と置換後の錐の全比較を各辺で読む。
方針：指定円柱による錐輸送の頂点・図式制限を評価する。
規約：頂点辺は恒等、図式辺は元の定値 path の切断。使われ方：元の射影の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {X Y Z : KanObject.{u}}

/-- 概要：元の cospan と置換 cospan の native 錐を結ぶ指定全円柱。
方針：構成済みの追跡可能な錐輸送。規約：元の頂点は固定。使われ方：脚の比較。 -/
def intervalPullbackConeHomotopy (f : X ⟶ Y) (g : Z ⟶ Y) :
    SSet.Homotopy (intervalPullbackCone f g).val (intervalPullbackReplacementCone f g).val :=
  (intervalPullbackStrictConeTransport f g).homotopy

/-- 概要：錐比較の頂点制限は全時刻で定値。
方針：指定輸送の左制限。規約：厳密な円柱。使われ方：頂点辺の恒等性。 -/
lemma intervalPullbackConeHomotopy_apex (f : X ⟶ Y) (g : Z ⟶ Y) :
    (joinInl _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (intervalPullbackConeHomotopy f g).h =
      CartesianMonoidalCategory.fst _ (Δ[1] : SSet.{u + 1}) ≫
        joinInl _ _ ≫ (intervalPullbackReplacementCone f g).val :=
  (intervalPullbackStrictConeTransport f g).apex

/-- 概要：錐比較の図式制限は元の切断の指定 coherent 円柱。
方針：指定輸送の右制限。規約：全単体。使われ方：図式辺の成分の回収。 -/
lemma intervalPullbackConeHomotopy_diagram (f : X ⟶ Y) (g : Z ⟶ Y) :
    (joinInr _ _ ▷ (Δ[1] : SSet.{u + 1})) ≫ (intervalPullbackConeHomotopy f g).h =
      (β_ _ (Δ[1] : SSet.{u + 1})).hom ≫ strictCoherentNatTransMap (intervalCospanSection f g) :=
  (intervalPullbackStrictConeTransport f g).diagram

/-- 概要：錐比較の頂点辺は元の path 引き戻しの恒等射の辺。
方針：定値頂点円柱を評価。規約：一単体の等式。使われ方：脚の正方形の簡約。 -/
lemma intervalPullbackConeHomotopy_apexEdge (f : X ⟶ Y) (g : Z ⟶ Y) :
    (coneHomotopyApexEdge (intervalPullbackConeHomotopy f g)).edge =
      (coherentNerveEdge (𝟙 (intervalPullbackKanObject f g))).edge := by
  let J := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan))
  have h := homotopyVertexEdge_constant (intervalPullbackConeHomotopy f g) (joinInl Δ[0] J)
    (joinInl Δ[0] J ≫ (intervalPullbackReplacementCone f g).val)
    (intervalPullbackConeHomotopy_apex f g) (SSet.yonedaEquiv (𝟙 Δ[0]))
  change (coneHomotopyApexEdge (intervalPullbackConeHomotopy f g)).edge =
    PinchedHom.constant (intervalPullbackReplacementCone f g).vertex 1 at h
  calc
    _ = _ := h
    _ = PinchedHom.constant (coherentNerveVertex (intervalPullbackKanObject f g)) 1 := by
      rw [intervalPullbackReplacementCone_vertex]
    _ = _ := by rw [coherentNerveEdge_id, pinchedConstant_one]; rfl

/-- 概要：錐比較の各図式辺は元の切断の指定成分の辺。
方針：指定 coherent 円柱の成分を評価。規約：全ての添字。使われ方：射影との比較。 -/
lemma intervalPullbackConeHomotopy_diagramEdge (f : X ⟶ Y) (g : Z ⟶ Y)
    (i : AsSmall.{u} WalkingCospan) :
    (coneHomotopyDiagramEdge (intervalPullbackConeHomotopy f g)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (coherentNerveEdge ((intervalCospanSection f g).app i)).edge := by
  have h := homotopyVertexEdge_prism (intervalPullbackConeHomotopy f g) (joinInr _ _)
    (strictCoherentNatTransMap (intervalCospanSection f g))
    (intervalPullbackConeHomotopy_diagram f g) (ULift.up (ComposableArrows.mk₀ i))
  exact h.trans (strictCoherentNatTransMap_component (intervalCospanSection f g) i)

end SerrePositivity.InfinityCategories.F2
