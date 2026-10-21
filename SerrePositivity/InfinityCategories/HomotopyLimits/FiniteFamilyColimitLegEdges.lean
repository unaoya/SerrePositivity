module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaPresheafColimitFiniteCone
public import SerrePositivity.InfinityCategories.HomotopyLimits.TotalKanNativeHomAction
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaPresheafOriginalLegComparison

/-!
概要：元の有限添字へ戻した余極限全錐の各辺を、元の評価脚の Kan 像へ厳密に照合する。
方針：同じ有限表示の再添字の両逆と、native 脚の Kan 読み戻しの厳密な式を使う。
規約：元の各添字・頂点・全一単体を保持する。
使われ方：実際の前層余極限脚の共役と、完成済み標準有限積錐の脚の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}} {J : Type u} [Finite J] [Nonempty J]
  (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
  (c : JoinCone (finiteFamilyFunctorDiagram G))
  (A : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (hA : c.vertex = functorVertex A)

/-- 元の添字に戻した同じ native 脚は、元の評価脚の全空間 Kan 像の全一単体。 -/
lemma finiteFamilyOriginalColimitFamilyCone_originalLeg_edge (j : J) :
    (F2.nativeConeLeg (finiteFamilyOriginalColimitFamilyCone G c A hA)
      (ULift.up (nerveVertex (Discrete.mk j)))).edge =
    (totalKanNativeEdge A (G j) (coherentTransformationTotalKanMap A (G j)
      (finiteFamilyOriginalLegTransformation G c A hA j))).edge := by
  let Q := nonemptyFiniteIndexPresentation J
  have h := F2.kanNativeConeLeg_edge (finiteFamilyOriginalColimitNativeCone G c A hA)
    (F2.coherentDiagramTotalKanObject A) (finiteFamilyOriginalColimitNativeCone_vertex G c A hA)
    (Discrete.mk (Q.2 j))
  rw [finiteFamilyOriginalColimitNativeCone_kanLeg] at h
  have hj : (nonemptyFiniteIndexPresentation J).2.symm (ULift.up (Q.2 j).down) = j :=
    Q.2.symm_apply_apply j
  calc
    _ = (F2.nativeConeLeg (finiteFamilyOriginalColimitNativeCone G c A hA)
        (ULift.up (ComposableArrows.mk₀ (Discrete.mk (Q.2 j))))).edge :=
      finiteFamilyOriginalColimitFamilyCone_leg_edge G c A hA (Discrete.mk j)
    _ = _ := h.symm.trans (congrArg (fun a => (totalKanNativeEdge A (G a)
      (coherentTransformationTotalKanMap A (G a)
        (finiteFamilyOriginalLegTransformation G c A hA a))).edge) hj)

variable {C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
  {p : nerve (Discrete J) ⟶ C.op} (d : JoinCone p)

/-- P_Σ の元の有限評価錐から得た標準全錐の各脚は、元の同じ評価脚の Kan 辺。 -/
lemma sigmaPresheafColimitFiniteCone_originalLeg_edge (j : J) :
    (F2.nativeConeLeg (sigmaPresheafColimitFiniteCone r d)
      (ULift.up (nerveVertex (Discrete.mk j)))).edge =
    (totalKanNativeEdge (sigmaPresheafVertexEvaluation r (JoinCone.ulift d).vertex)
      (sigmaPresheafFiniteEvaluationFamily r (p := p) j)
      (coherentTransformationTotalKanMap
        (sigmaPresheafVertexEvaluation r (JoinCone.ulift d).vertex)
        (sigmaPresheafFiniteEvaluationFamily r (p := p) j)
        (sigmaPresheafConeLegTransformation r d j))).edge :=
  finiteFamilyOriginalColimitFamilyCone_originalLeg_edge _ _ _ _ j

end SerrePositivity.InfinityCategories.HomotopyLimits
