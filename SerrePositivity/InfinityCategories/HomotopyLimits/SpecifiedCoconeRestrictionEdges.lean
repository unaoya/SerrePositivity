module

public import SerrePositivity.InfinityCategories.HomotopyLimits.EquivalencePathVertexEdge
public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitSpecifiedPathCocone

/-!
概要：指定経路で構成した余錐の両制限を fiber の点として計算し、右修正経路自身の辺を保持する。
方針：経路付き貼り合わせの射の式を零単体で評価し、経路の辺の自然性で境界への像を計算する。
規約：右修正の辺は別の代表へ選び直さない。使われ方：共通 end の経路の整合性の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))

/-- 固定終点の余錐空間の制限は、包含後に元の余錐の制限そのものになる。 -/
lemma coconeRestrictionFiber_vertex_val {K L X : SSet.{u}} {F : K ⟶ X}
    (a : L ⟶ K) (y : X _⦋0⦌) (v : (coconeMappingSpace F y) _⦋0⦌) :
    ((cosliceRestrictionFiberMap F a y).app (Opposite.op ⦋0⦌) v).val =
      JoinCocone.restrict v.val a := by
  rfl

/-- 指定経路で作った余錐を、指定した元の span 頂点上の fiber の点として保持する。 -/
def partialColimitSpecifiedFiberVertex : (coconeMappingSpace p
    (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
      g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).vertex) _⦋0⦌ :=
  SSet.yonedaEquiv (partialColimitSpecifiedBoundaryFamily hp p c hc dB dC)

/-- 左制限の fiber の点は、実際の左脚で輸送した元の左余錐。 -/
lemma partialColimitSpecifiedFiberVertex_left :
    (cosliceRestrictionFiberMap p i _).app (Opposite.op ⦋0⦌)
        (partialColimitSpecifiedFiberVertex hp p c hc dB dC) =
      transportedCoconeVertex dB (partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC) := by
  have h := congrArg SSet.yonedaEquiv (partialColimitSpecifiedBoundaryFamily_left hp p c hc dB dC)
  rw [SSet.yonedaEquiv_comp] at h
  exact h.trans (SSet.yonedaEquiv.apply_symm_apply _)

/-- 右制限の fiber の点は、指定した修正経路の終点。 -/
lemma partialColimitSpecifiedFiberVertex_right :
    (cosliceRestrictionFiberMap p j _).app (Opposite.op ⦋0⦌)
        (partialColimitSpecifiedFiberVertex hp p c hc dB dC) =
      (equivalencePathEndpoint _ 1).app (Opposite.op ⦋0⦌)
        (SSet.yonedaEquiv (partialColimitSpecifiedBoundaryCorrection hp p c hc dB dC)) := by
  have h := congrArg SSet.yonedaEquiv (partialColimitSpecifiedBoundaryFamily_right hp p c hc dB dC)
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp] at h
  exact h

/-- 右修正経路の始点は、実際の右脚で輸送した元の右余錐。 -/
lemma partialColimitSpecifiedCorrection_zero :
    (equivalencePathEndpoint _ 0).app (Opposite.op ⦋0⦌)
        (SSet.yonedaEquiv (partialColimitSpecifiedBoundaryCorrection hp p c hc dB dC)) =
      transportedCoconeVertex dC (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC) := by
  have h := congrArg SSet.yonedaEquiv
    (coconeBoundaryPathCorrection_zero hp p _
      (SSet.yonedaEquiv.symm (transportedCoconeVertex dC
        (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)))
      (partialColimitSpanBoundaryPath c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
      (partialColimitSpanBoundaryPath_zero c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
  rw [SSet.yonedaEquiv_comp] at h
  exact h.trans (SSet.yonedaEquiv.apply_symm_apply _)

/-- 指定した右修正経路自身の、元の右輸送像から貼った余錐の右制限への辺。 -/
def partialColimitSpecifiedCorrectionEdge :
    (coconeMappingSpace (j ≫ p) _).Edge
      (transportedCoconeVertex dC (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
      ((cosliceRestrictionFiberMap p j _).app (Opposite.op ⦋0⦌)
        (partialColimitSpecifiedFiberVertex hp p c hc dB dC)) :=
  ⟨(equivalencePathVertexEdge
      (SSet.yonedaEquiv (partialColimitSpecifiedBoundaryCorrection hp p c hc dB dC))).edge,
    (equivalencePathVertexEdge _).src_eq.trans
      (partialColimitSpecifiedCorrection_zero hp p c hc dB dC),
    (equivalencePathVertexEdge _).tgt_eq.trans
      (partialColimitSpecifiedFiberVertex_right hp p c hc dB dC).symm⟩

/-- 修正辺の境界への像は、普遍 span の二単体から作った指定境界経路自身の辺。 -/
lemma partialColimitSpecifiedCorrectionEdge_projection :
    (normalizedCoconeRestrictionFiber (j ≫ p) g (coconePushoutBoundary_eq hp p)
        (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).vertex).app (Opposite.op ⦋1⦌)
        (partialColimitSpecifiedCorrectionEdge hp p c hc dB dC).edge =
      intervalFunctorVertexEdge (SSet.yonedaEquiv
        (partialColimitSpanBoundaryPath c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).val := by
  have h := congrArg SSet.yonedaEquiv
    (partialColimitSpecifiedBoundaryCorrection_projection hp p c hc dB dC)
  rw [SSet.yonedaEquiv_comp] at h
  have hh := equivalencePathVertexEdge_map
    (normalizedCoconeRestrictionFiber (j ≫ p) g (coconePushoutBoundary_eq hp p)
      (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).vertex)
    (SSet.yonedaEquiv (partialColimitSpecifiedBoundaryCorrection hp p c hc dB dC))
  have he := congrArg (fun v : (equivalencePath (coconeMappingSpace (f ≫ (i ≫ p))
      (partialColimitStrictSpanCocone c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC).vertex)) _⦋0⦌ ↦
    intervalFunctorVertexEdge v.val) h
  exact hh.trans he

/-- 右修正経路自身の辺を、実際の余錐の右制限を終点とする coslice の辺として表示する。 -/
def partialColimitSpecifiedCorrectionCosliceEdge :
    (sliceUnder (j ≫ p)).Edge
      (transportedCoconeVertex dC (partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)).val
      ((partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict j) :=
  ⟨(partialColimitSpecifiedCorrectionEdge hp p c hc dB dC).edge.val,
    congrArg Subtype.val (partialColimitSpecifiedCorrectionEdge hp p c hc dB dC).src_eq,
    (congrArg Subtype.val (partialColimitSpecifiedCorrectionEdge hp p c hc dB dC).tgt_eq).trans
      (coconeRestrictionFiber_vertex_val j _
        (partialColimitSpecifiedFiberVertex hp p c hc dB dC))⟩

end
end SerrePositivity.InfinityCategories.HomotopyLimits
