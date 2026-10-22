module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SiftedOppositeProducts
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaDensityCocone
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaYonedaEvaluation

/-!
概要：元の P_Σ 対象を、元の小さい sifted な元の圏上の Yoneda 余極限として表す。
方針：反変関手の有限積保存で全空間の有限積を構成し、反転して sifted 性を得る。
規約：有限余積の仮定は Cᵒᵖ の全有限積の存在で明示。指定 P_Σ 頂点を厳密に保持。
使われ方：P-1 g の sifted 生成と、元の Yoneda に沿う全左 Kan 延長の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の内部密度余錐の頂点は、包含後に元の前層自身を厳密に回収する。 -/
lemma sigmaDensityCocone_vertex {C : SSet.{u}} [Quasicategory C]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (hF : IsSigmaPresheaf (functorVertex F)) :
    (sigmaPresheafInfinityInclusion C).app (Opposite.op ⦋0⦌)
      (sigmaDensityCocone F hF).vertex = functorVertex F := by
  have h := congrArg JoinCocone.vertex (sigmaDensityCocone_inclusion F hF)
  exact h.trans (sigmaDensityAmbientCocone_vertex F)

/-- 有限余積を積へ送る元の前層の、元の小さい元の圏自身が sifted。 -/
lemma sigmaPresheafElements_isSifted {C : SSet.{u}} [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), HasLimit d)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (hF : PreservesFiniteProductsFromSmallSource F) :
    IsSiftedInfinity (smallRightUnstraightening F) := by
  have : Quasicategory (smallLeftUnstraightening F) :=
    quasicategory_of_innerFibration (smallLeftUnstraighteningProjection F)
  change IsSiftedInfinity (smallLeftUnstraightening F).op
  apply isSiftedInfinity_op_of_hasFiniteProducts (smallLeftUnstraightening F)
  intro J hJ d
  exact hasLimit_smallLeftUnstraightening_of_finiteProducts F hF d
    (hC J (d ≫ smallLeftUnstraighteningProjection F))

/-- 各元の P_Σ 対象は、小さい sifted ∞ 圏上の同じ Yoneda 図式の余極限。 -/
lemma sigmaPresheaf_siftedPresentation (C : SSet.{u}) [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), HasLimit d)
    (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    ∃ (B : SSet.{u}) (p : B ⟶ C)
      (c : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map p ≫ sigmaYonedaInfinityMap C)),
      Quasicategory B ∧ IsSiftedInfinity B ∧ c.vertex = v ∧ IsColimitCone c := by
  let F := sigmaPresheafVertexFunctor v
  have hSigma : IsSigmaPresheaf (functorVertex F) := by
    change IsSigmaPresheaf (functorVertex (sigmaPresheafVertexFunctor v))
    rw [sigmaPresheafVertexFunctor_vertex]
    exact sigmaPresheafInfinity_vertex v
  let c := sigmaDensityCocone F hSigma
  have hv : c.vertex = v := by
    apply Subtype.ext
    exact (sigmaDensityCocone_vertex F hSigma).trans (sigmaPresheafVertexFunctor_vertex v)
  exact ⟨smallRightUnstraightening F, smallRightUnstraighteningProjection F, c,
    inferInstance, sigmaPresheafElements_isSifted hC F
      (sigmaPresheafVertexFunctor_preservesFiniteProducts v), hv,
    sigmaDensityCocone_isColimit F hSigma⟩

/-- 元の Yoneda 像を含み小さい sifted 余極限で閉じる頂点条件は、全 P_Σ 対象を含む。 -/
lemma sigmaPresheaf_sifted_induction (C : SSet.{u}) [Quasicategory C]
    (hC : ∀ (J : Type u) [Finite J] (d : nerve (Discrete J) ⟶ C.op), HasLimit d)
    (P : (SigmaPresheafInfinity C) _⦋0⦌ → Prop)
    (hY : ∀ x : C _⦋0⦌,
      P ((sigmaYonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up x)))
    (hcolim : ∀ (B : SSet.{u}) [Quasicategory B] [IsSiftedInfinity B]
      (D : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
      (c : JoinCocone D), IsColimitCone c →
      (∀ b : B _⦋0⦌, P (D.app (Opposite.op ⦋0⦌) (ULift.up b))) → P c.vertex) :
    ∀ v : (SigmaPresheafInfinity C) _⦋0⦌, P v := by
  intro v
  obtain ⟨B, p, c, hB, hS, hv, hc⟩ := sigmaPresheaf_siftedPresentation C hC v
  have : Quasicategory B := hB
  have : IsSiftedInfinity B := hS
  have h := hcolim B _ c hc (fun b => hY (p.app (Opposite.op ⦋0⦌) b))
  rwa [hv] at h

end SerrePositivity.InfinityCategories.HomotopyLimits
