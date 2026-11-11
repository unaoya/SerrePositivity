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
  (ε₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (Q₁.comp L₁) (DGFunctor.id C))
  (ε₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (Q₂.comp L₂) (DGFunctor.id D))

/-- まず元の第一余単位を第二延長で写し、続いて元の第二余単位を適用する。 -/
def dgStrictCompositeCounit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans ((Q₂.comp Q₁).comp (L₁.comp L₂)) (DGFunctor.id D) where
  app x := by
    let a : zeroCycles (homObject R D (L₂.obj (L₁.obj (Q₁.obj (Q₂.obj x))))
        (L₂.obj (Q₂.obj x))) :=
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp Q₂ ε₁) L₂).app x
    let b : zeroCycles (homObject R D (L₂.obj (Q₂.obj x)) x) := ε₂.app x
    refine ⟨compose R b.val a.val (zero_add 0), ?_⟩
    change differential R (compose R b.val a.val (zero_add 0)) = 0
    have ha : differential R a.val = 0 := a.property
    have hb : differential R b.val = 0 := b.property
    rw [differential_compose, ha, hb]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero, smul_zero, zero_add]
  naturality {x y k} f := by
    let a := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp Q₂ ε₁) L₂
    have ha := a.naturality f
    change compose R (a.app y).val
        (((L₁.comp L₂).map _ _).f k (((Q₂.comp Q₁).map x y).f k f)) (add_zero k) =
      compose R (((Q₂.comp L₂).map x y).f k f) (a.app x).val (zero_add k) at ha
    have hb := ε₂.naturality f
    change compose R (ε₂.app y).val (((Q₂.comp L₂).map x y).f k f) (add_zero k) =
      compose R f (ε₂.app x).val (zero_add k) at hb
    change compose R (compose R (ε₂.app y).val (a.app y).val (zero_add 0))
        (((L₁.comp L₂).map _ _).f k (((Q₂.comp Q₁).map x y).f k f)) (add_zero k) =
      compose R f (compose R (ε₂.app x).val (a.app x).val (zero_add 0)) (zero_add k)
    calc
      _ = compose R (ε₂.app y).val
          (compose R (a.app y).val
            (((L₁.comp L₂).map _ _).f k (((Q₂.comp Q₁).map x y).f k f))
              (add_zero k)) (add_zero k) :=
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (add_zero k) (zero_add 0) (add_zero k)).symm
      _ = compose R (ε₂.app y).val
          (compose R (((Q₂.comp L₂).map x y).f k f) (a.app x).val (zero_add k))
            (add_zero k) := by rw [ha]
      _ = compose R (compose R (ε₂.app y).val
          (((Q₂.comp L₂).map x y).f k f) (add_zero k)) (a.app x).val (zero_add k) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (zero_add k) (add_zero k) (add_zero k)
      _ = compose R (compose R f (ε₂.app x).val (zero_add k))
          (a.app x).val (zero_add k) := by rw [hb]
      _ = _ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NestedCut.compose_assoc_of_sum _ _ _ (zero_add 0) (zero_add k) (zero_add k)).symm

end SerrePositivity.KST.LocalizingInvariants
