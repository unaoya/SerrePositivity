module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCoefficientChartPullback
public import SerrePositivity.AlgebraicGeometry.ProjectiveCoefficientStructureMap

/-!
概要：次数一の標準開で覆われる Proj の任意の係数移送は pullback。
方針：標準開の局所的な二つの Cartesian な四角形を、開被覆による判定へ渡す。
規約：係数移送の平坦性・Noether 性は不要。
使われ方：射影的なブローアップの任意の底変換の入力。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
universe u v
variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]
variable (G : ℕ → Submodule R A) [GradedRing G]

set_option backward.isDefEq.respectTransparency false in
/-- 次数一の標準開で覆われる Proj の係数移送は、同じ構造射の実際の pullback。 -/
theorem isPullback_projectiveCoefficientMap {ι : Type v} (a : ι → A)
    (ha : ∀ i, a i ∈ G 1)
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span (Set.range a)) :
    IsPullback (projectiveCoefficientMap (B := B) G)
      (projectiveCechStructureMap (fun n ↦ (G n).baseChange B))
      (projectiveCechStructureMap G) (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  let 𝒰 := (Proj.affineOpenCoverOfIrrelevantLESpan G a ha
    (fun _ ↦ by decide : ∀ _ : ι, 0 < 1) hspan).openCover
  apply Scheme.isPullback_of_openCover _ _ _ _ 𝒰
  intro i
  change IsPullback
    (pullback.snd (projectiveCoefficientMap (B := B) G) (Proj.awayι G (a i) (ha i) (by decide)))
    (pullback.fst (projectiveCoefficientMap (B := B) G) (Proj.awayι G (a i) (ha i) (by decide)) ≫
      projectiveCechStructureMap (fun n ↦ (G n).baseChange B))
    (Proj.awayι G (a i) (ha i) (by decide) ≫ projectiveCechStructureMap G) _
  let H := isPullback_projectiveCoefficientAwayι (B := B) G (ha i) (by decide)
  have hlocal : IsPullback
      (Spec.map (CommRingCat.ofHom
        (HomogeneousLocalization.Away.map (projectiveCoefficientGradedMap (B := B) G) (a i))))
      (Proj.awayι (fun n ↦ (G n).baseChange B) ((1 : B) ⊗ₜ[R] a i)
        (Submodule.tmul_mem_baseChange_of_mem (1 : B) (ha i)) (by decide) ≫
          projectiveCechStructureMap (fun n ↦ (G n).baseChange B))
      (Proj.awayι G (a i) (ha i) (by decide) ≫ projectiveCechStructureMap G)
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
    rw [projectiveAway_structureMap, projectiveAway_structureMap]
    exact isPullback_projectiveCoefficientChart (B := B) G (ha i)
  refine hlocal.of_iso H.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ?_ ?_ (by simp) (by simp)
  · simpa only [Iso.refl_hom, Category.comp_id] using H.flip.isoPullback_hom_snd.symm
  · simpa only [Iso.refl_hom, Category.comp_id, Category.assoc] using
      (H.flip.isoPullback_hom_fst_assoc
        (projectiveCechStructureMap (fun n ↦ (G n).baseChange B))).symm

end SerrePositivity.AlgebraicGeometry
