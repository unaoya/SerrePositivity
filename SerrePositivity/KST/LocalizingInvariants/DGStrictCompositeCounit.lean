module

public import SerrePositivity.KST.LocalizingInvariants.DGStrictAdjointComparison

/-!
概要：二つの元の厳密 dg 余単位を、合成随伴の式を持つ厳密 dg 余単位へ束ねる。
方針：前後合成と厳密変換の合成を使い、dg 関手の実結合則で始域を同定する。
規約：同じ四つの dg 関手を保持。使われ方：graph 延長の実合成比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.InfinityCategories.DGNerve
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {B C D E : Type v}
  [DGCategory R B] [DGCategory R C] [DGCategory R D] [DGCategory R E]

lemma dgFunctorComp_assoc (F : DGFunctor R B C) (G : DGFunctor R C D)
    (H : DGFunctor R D E) : (F.comp G).comp H = F.comp (G.comp H) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, eqToHom_refl, Category.comp_id, Category.assoc]

lemma dgFunctorComp_id (F : DGFunctor R B C) : F.comp (DGFunctor.id C) = F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, EnrichedFunctor.id_map, eqToHom_refl, Category.comp_id]

lemma dgFunctorId_comp (F : DGFunctor R B C) : (DGFunctor.id B).comp F = F := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  simp only [EnrichedFunctor.comp_map, EnrichedFunctor.id_map, eqToHom_refl,
    Category.comp_id, Category.id_comp]

variable (L₁ : DGFunctor R B C) (L₂ : DGFunctor R C D)
  (Q₁ : DGFunctor R C B) (Q₂ : DGFunctor R D C)
  (ε₁ : StrictNatTrans (Q₁.comp L₁) (DGFunctor.id C))
  (ε₂ : StrictNatTrans (Q₂.comp L₂) (DGFunctor.id D))

/-- まず元の第一余単位を第二延長で写し、続いて元の第二余単位を適用する。 -/
def dgStrictCompositeCounit :
    StrictNatTrans ((Q₂.comp Q₁).comp (L₁.comp L₂)) (DGFunctor.id D) := by
  let a := dgStrictNatTransPostcomp (dgStrictNatTransPrecomp Q₂ ε₁) L₂
  have hs : (Q₂.comp (Q₁.comp L₁)).comp L₂ = (Q₂.comp Q₁).comp (L₁.comp L₂) :=
    (dgFunctorComp_assoc Q₂ (Q₁.comp L₁) L₂).trans
      ((congrArg (fun H => Q₂.comp H) (dgFunctorComp_assoc Q₁ L₁ L₂)).trans
        (dgFunctorComp_assoc Q₂ Q₁ (L₁.comp L₂)).symm)
  have ht : (Q₂.comp (DGFunctor.id C)).comp L₂ = Q₂.comp L₂ :=
    congrArg (fun H => H.comp L₂) (dgFunctorComp_id Q₂)
  rw [hs, ht] at a
  exact dgStrictNatTransComp a ε₂

end SerrePositivity.KST.LocalizingInvariants
