module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionCofinal
public import SerrePositivity.InfinityCategories.F2.Idempotent.SliceCanonicalCocone
public import SerrePositivity.InfinityCategories.F1B.CofinalAnodyneRecognition
public import SerrePositivity.InfinityCategories.Stable.PastingRightCocone

/-!
概要：元の全部分圏の冪等完備化に沿って、全関手の元の標準左 Kan 余錐が余極限。
方針：slice 上の冪等完備化の right cofinal 性で元の全 slice の標準余錐を制限する。
規約：元の包含そのものと全余錐を保持し、点での同型だけで代用しない。
使われ方：HTT 5.1.4.7、制限関手の全写像空間での充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の標準左 Kan 余錐は、元の全 slice の標準余錐を同じ元の射影で制限したもの。 -/
lemma leftKanCanonicalCocone_slice_restrict_val {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    (leftKanCanonicalCocone δ F c).val =
      joinMap (pullback.snd δ (sliceOverProjection (SSet.yonedaEquiv.symm c)))
        (𝟙 (Δ[0] : SSet.{u})) ≫ (sliceCanonicalCocone F c).val := by
  change sliceOverUncurry _ ≫ F = joinMap _ _ ≫ (sliceOverUncurry _ ≫ F)
  rw [← Category.assoc, ← sliceOverUncurry_precomp, Category.comp_id]

/-- 元の全部分圏の冪等完備化に沿う全関手の元の全標準左 Kan 余錐は余極限。 -/
lemma IsIdempotentCompletion.canonicalCocones_isColimit {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) [Mono δ] [InnerFibration δ] (hδ : IsIdempotentCompletion δ)
    (F : C ⟶ D) (c : C _⦋0⦌) : IsColimitCone (leftKanCanonicalCocone δ F c) := by
  let q := sliceOverProjection (SSet.yonedaEquiv.symm c)
  have : InnerFibration (pullback.snd δ q) :=
    ⟨innerFibrations.pullback_snd δ q (InnerFibration.mem (q := δ))⟩
  have : Quasicategory (pullback δ q) := quasicategory_of_innerFibration (pullback.snd δ q)
  have hc := IsIdempotentCompletion.sliceOver δ hδ (SSet.yonedaEquiv.symm c)
  have hr := IsIdempotentCompletion.isRightCofinal (pullback.snd δ q) hc
  have h := (sliceCanonicalCocone_isColimit F c).restrict_of_rightAnodyne
    (pullback.snd δ q) hr.rightAnodyneExtensions
  exact (isColimitCone_iff_of_val_eq (leftKanCanonicalCocone δ F c)
    ((sliceCanonicalCocone F c).restrict (pullback.snd δ q))
    (leftKanCanonicalCocone_slice_restrict_val δ F c)).mpr h

end SerrePositivity.InfinityCategories.F2.Idempotent
