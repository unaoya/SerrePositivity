module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaPresheafLegBottom
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteFamilyColimitLegEdges

/-!
概要：標準有限評価余極限錐の元の各脚と、実際の頂点脚の共役の Hom 類を照合する。
方針：同じ評価脚の変換頂点と、同じ元の Kan 辺の厳密な読み戻しを使う。
規約：元の添字・標準全錐・実際の余錐・同じ共役比較を保持する。
使われ方：実際の頂点関手による有限錐像へ標準全錐の極限性を移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open SSet.Truncated.HomotopyCategory
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
  (q : JoinCocone (r ≫ sigmaPresheafInfinityInclusion C))
  (hq : ∀ x : ((SSet.uliftFunctor.{u + 1, u}).obj C.op) _⦋0⦌,
    IsColimitCone (F1B.kanPostcomposeCocone (evaluateFunctorAt x) q))
  {J : Type u} {p : nerve (Discrete J) ⟶ C.op} (c : JoinCone p) (j : J)
local notation "x₀" => JoinCone.vertex (JoinCone.ulift c)
local notation "A" => sigmaPresheafVertexEvaluation r x₀
local notation "G" => sigmaPresheafFiniteEvaluationFamily r (p := p)

/-- 同じ元の有限評価脚の Kan 辺と、実際の頂点脚の共役は同じ類。 -/
lemma sigmaPresheafColimitLegConjugate_kanHomMk :
    homMk (totalKanNativeEdge A (G j) (coherentTransformationTotalKanMap A (G j)
      (sigmaPresheafConeLegTransformation r c j))).toTruncated =
    homMk (presheafColimitLegConjugate q hq c
      (ULift.up (nerveVertex (Discrete.mk j)))).toTruncated := by
  have h := presheafColimitLegConjugate_homMk q hq c
    (ULift.up (nerveVertex (Discrete.mk j)))
  change homMk (totalKanNativeEdge A (G j) (coherentTransformationTotalKanMap A (G j)
    (intervalMappingVertexOfEdge (sigmaPresheafCoconeBottomLeg r q c j)))).toTruncated = _ at h
  rw [sigmaPresheafCoconeBottomLeg_vertex] at h
  exact h

variable [Finite J] [Nonempty J]

/-- 元の標準有限評価余極限全錐の頂点は、同じ頂点評価の余極限 Kan 対象。 -/
lemma sigmaPresheafColimitFiniteCone_vertex :
    (sigmaPresheafColimitFiniteCone r c).vertex =
      coherentNerveVertex (F2.coherentDiagramTotalKanObject A) :=
  finiteFamilyOriginalColimitFamilyCone_vertex _ _ _ _

/-- 元の標準全錐の同じ脚を、同じ余極限余錐頂点と指定 Kan 頂点の端点表示で保持。 -/
def sigmaPresheafStandardColimitLeg :
    SSet.Edge (F2.coherentDiagramTotalCocone A).vertex (F2.coherentDiagramTotalVertex (G j)) :=
  (SSet.Edge.ofTruncated (F2.nativeConeLeg (sigmaPresheafColimitFiniteCone r c)
    (ULift.up (nerveVertex (Discrete.mk j))))).ofEq
      ((sigmaPresheafColimitFiniteCone_vertex r c).trans
        ((spaceInfinityVertex_eq_coherent (F2.coherentDiagramTotalKanObject A)).symm.trans
          (F2.coherentDiagramTotalCocone_vertex A).symm))
      (kanDiagramCoherentNerve_vertex (Discrete.functor
        (fun k => F2.coherentDiagramTotalKanObject (G k))) (Discrete.mk j))

/-- 標準有限評価全錐から取った同じ脚は、元の同じ評価脚の全空間 Kan 辺そのもの。 -/
lemma sigmaPresheafStandardColimitLeg_eq :
    sigmaPresheafStandardColimitLeg r c j =
      totalKanNativeEdge A (G j) (coherentTransformationTotalKanMap A (G j)
        (sigmaPresheafConeLegTransformation r c j)) :=
  SSet.Edge.ext (sigmaPresheafColimitFiniteCone_originalLeg_edge r c j)

/-- 同じ標準有限積全錐の各脚と、実際の頂点脚の同じ共役辺は同じ Hom 類。 -/
lemma sigmaPresheafStandardColimitLeg_homMk :
    homMk (sigmaPresheafStandardColimitLeg r c j).toTruncated =
      homMk (presheafColimitLegConjugate q hq c
        (ULift.up (nerveVertex (Discrete.mk j)))).toTruncated := by
  rw [sigmaPresheafStandardColimitLeg_eq]
  exact sigmaPresheafColimitLegConjugate_kanHomMk r q hq c j

end SerrePositivity.InfinityCategories.HomotopyLimits
