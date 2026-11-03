module

public import SerrePositivity.InfinityCategories.F2.Idempotent.ImageCanonicalCocone
public import SerrePositivity.InfinityCategories.F1.Idempotent.StrongSplittingColimit
public import SerrePositivity.InfinityCategories.F1B.Idempotent.IdemInclusionFull
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftIdentityLeg

/-!
概要：元の任意の強分裂図式の全標準左 Kan 余錐は、同じ全余錐のまま余極限。
方針：非分裂対象では元の恒等頂点、分裂対象では元の Idem 余錐の厳密な照合を使う。
規約：関手と全局所余錐を選び直さない。
使われ方：元の前合成の全写像空間での充満忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の任意の図式で後合成した標準余錐は、同じ全 Idem 余錐の元の射影への制限。 -/
lemma idemImageCanonicalCocone_postcomp {X : SSet.{u}} (F : SplitShape ⟶ X) :
    (leftKanCanonicalCocone idemInclusion F (nerveVertex walkingImage)).val =
      joinMap (leftKanProjection idemInclusion (nerveVertex walkingImage)) (𝟙 (Δ[0] : SSet.{u})) ≫
        (walkingJoinCocone.val ≫ F) := by
  have h := congrArg (fun f ↦ f ≫ F) idemImageCanonicalCocone_eq.{u}
  exact h.trans (Category.assoc _ _ _)

/-- 元の分裂対象での標準余錐そのものは、元の厳密な分裂余錐により余極限。 -/
lemma idemImageCanonicalCocone_isColimit {X : SSet.{u}} [Quasicategory X]
    (F : SplitShape ⟶ X) :
    IsColimitCone (leftKanCanonicalCocone idemInclusion F (nerveVertex walkingImage)) := by
  let s : StrongSplitting (idemInclusion ≫ F) := ⟨F, rfl⟩
  let p := leftKanProjection idemInclusion (nerveVertex walkingImage.{u})
  have he : leftKanCanonicalCocone idemInclusion F (nerveVertex walkingImage) =
      s.cocone.restrict p := Subtype.ext (idemImageCanonicalCocone_postcomp F)
  rw [he]
  exact (isColimitCone_iff_restrict_of_isIso s.cocone p).mp s.cocone_isColimit

/-- 元の全強分裂図式は、元の全 Idem 包含に沿う全標準局所余極限条件を満たす。 -/
lemma splittingCanonicalCocones_isColimit {X : SSet.{u}} [Quasicategory X]
    (F : SplitShape ⟶ X) (b : SplitShape _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone idemInclusion F b) := by
  obtain ⟨P, rfl⟩ := (nerveEquiv (C := WalkingSplit.{u})).symm.surjective b
  rcases walkingSplit_object_cases P with h | h
  · subst P
    exact F1B.kanLeftCanonical_isColimit_at_image idemInclusion
      idemInclusion_isFullyFaithful F (nerveVertex walkingObject)
  · subst P
    exact idemImageCanonicalCocone_isColimit F

end SerrePositivity.InfinityCategories.F2.Idempotent
