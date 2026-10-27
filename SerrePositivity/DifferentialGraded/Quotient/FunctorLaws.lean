module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFunctoriality

/-!
概要：固定標準 ε を保つ正本商関手の、厳密な恒等・合成と元 Hom 作用。
方針：同じ指定収縮付き普遍性で関手全体を照合する。
規約：関手変数の任意の自然変換の延長は主張しない。
使われ方：ε 整合関手圏の横の単位・合成則。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t s
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory
private lemma functorAssoc {R : Type u} [CommRing R]
    {X : Type v} {Y : Type w} {Z : Type t} {W : Type s}
    [DGCategory R X] [DGCategory R Y] [DGCategory R Z] [DGCategory R W]
    (a : DGFunctor R X Y) (b : DGFunctor R Y Z) (c : DGFunctor R Z W) :
    (a.comp b).comp c = a.comp (b.comp c) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, eqToHom_refl,
    Category.comp_id, Category.assoc]

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

/-- 正本商関手は元の恒等関手を厳密に保つ。 -/
lemma quotientDGFunctor_id (S : Set C) :
    quotientDGFunctor R C C (DGFunctor.id C) S S (fun _ hx => hx) =
      DGFunctor.id (QuotientObject C S) := by
  apply (universalEquiv R C S (QuotientObject C S)).injective
  change restrictContractedFunctor R C S (extension R _) = _
  rw [restrict_extension]
  apply ContractedFunctor.ext R
  · change (DGFunctor.id C).comp (inclusion R C S) =
      (inclusion R C S).comp (DGFunctor.id _)
    apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
    intro x y
    simp only [DGFunctor.comp, DGFunctor.id, EnrichedFunctor.comp_map,
      EnrichedFunctor.id_map, eqToHom_refl, Category.comp_id, Category.id_comp]
  · exact heq_of_eq (funext (fun _ => rfl))

variable (D : Type w) [DGCategory R D] [Small.{u} D] (F : DGFunctor R C D)
  (S : Set C) (T : Set D) (hF : ∀ x ∈ S, F.obj x ∈ T)

/-- 元の全 Hom 鎖写像は、同じ商包含の下で厳密に回収される。 -/
lemma quotientDGFunctor_original (x y : C) :
    (inclusion R C S).map x y ≫
        (quotientDGFunctor R C D F S T hF).map ⟨x⟩ ⟨y⟩ =
      F.map x y ≫ (inclusion R D T).map (F.obj x) (F.obj y) :=
  quotientEvaluation_original R (functorContracted R C D F S T hF) x y

variable (E : Type t) [DGCategory R E] [Small.{u} E] (G : DGFunctor R D E)
  (U : Set E) (hG : ∀ x ∈ T, G.obj x ∈ U)

/-- 正本商関手は同じ標準 ε を保つ関手の元の合成を厳密に保つ。 -/
lemma quotientDGFunctor_comp :
    quotientDGFunctor R C E (F.comp G) S U (fun x hx => hG _ (hF x hx)) =
      (quotientDGFunctor R C D F S T hF).comp (quotientDGFunctor R D E G T U hG) := by
  let qF := quotientDGFunctor R C D F S T hF
  let qG := quotientDGFunctor R D E G T U hG
  apply (universalEquiv R C S (QuotientObject E U)).injective
  change restrictContractedFunctor R C S (extension R _) =
    restrictContractedFunctor R C S (qF.comp qG)
  rw [restrict_extension, restrictContractedFunctor_comp]
  have hqF : restrictContractedFunctor R C S qF = functorContracted R C D F S T hF :=
    restrict_extension R _
  rw [hqF]
  apply ContractedFunctor.ext R
  · change (F.comp G).comp (inclusion R E U) = (F.comp (inclusion R D T)).comp qG
    have h := quotientDGFunctor_inclusion R D E G T U hG
    calc
      (F.comp G).comp (inclusion R E U) = F.comp (G.comp (inclusion R E U)) := functorAssoc _ _ _
      _ = F.comp ((inclusion R D T).comp qG) := congrArg (F.comp) h.symm
      _ = (F.comp (inclusion R D T)).comp qG := (functorAssoc _ _ _).symm
  · apply heq_of_eq
    funext b
    exact (quotientDGFunctor_epsilon R D E G T U hG ⟨F.obj b.val, hF b.val b.property⟩).symm

end SerrePositivity.DifferentialGraded.DGQuotient
