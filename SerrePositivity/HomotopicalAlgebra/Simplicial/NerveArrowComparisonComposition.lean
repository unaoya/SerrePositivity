module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveArrowComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveBiparameterComposition

/-! # Exact endpoint calculus for composable changes of coherent centers -/

@[expose] public section
universe w uD vD uE vE
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.SimplicialModel.NerveArrowComparisonComposition
open NerveBiparameterMaps
variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  (K F : D ⥤ SSet.{w}) (a : NerveBiparameter.System K F)
  (H J L : E ⥤ D) (τ : H ⟶ J) (σ : J ⟶ L)

def leftAlong : NerveBiparameter.System (H ⋙ K) (J ⋙ F) :=
  mapTarget _ _ _ (Functor.whiskerRight τ F) (reindex K F H a)

def rightAlong : NerveBiparameter.System (H ⋙ K) (J ⋙ F) :=
  restrict _ _ _ (Functor.whiskerRight τ K) (reindex K F J a)

lemma left_follow : mapTarget _ _ _ (Functor.whiskerRight σ F) (leftAlong K F a H J τ) =
    leftAlong K F a H L (τ ≫ σ) := by
  change (reindex K F H a ≫ targetMap _ _ _ _) ≫ targetMap _ _ _ _ = _
  rw [Category.assoc, targetMap_comp, ← Functor.whiskerRight_comp]
  rfl

lemma right_precede : restrict _ _ _ (Functor.whiskerRight τ K) (rightAlong K F a J L σ) =
    rightAlong K F a H L (τ ≫ σ) := by
  change (reindex K F L a ≫ restriction _ _ _ _) ≫ restriction _ _ _ _ = _
  rw [Category.assoc, restriction_comp, ← Functor.whiskerRight_comp]
  rfl

lemma middle_exchange : mapTarget _ _ _ (Functor.whiskerRight σ F) (rightAlong K F a H J τ) =
    restrict _ _ _ (Functor.whiskerRight τ K) (leftAlong K F a J L σ) := by
  change (reindex K F J a ≫ restriction _ _ _ _) ≫ targetMap _ _ _ _ =
    (reindex K F J a ≫ targetMap _ _ _ _) ≫ restriction _ _ _ _
  rw [Category.assoc, ← target_restriction, ← Category.assoc]

lemma right_follow_eq (h : J = L) : mapTarget _ _ _ (Functor.whiskerRight (eqToHom h) F)
    (rightAlong K F a H J τ) = rightAlong K F a H L (τ ≫ eqToHom h) := by
  have heq : reindex K F J a ≫ targetMap (J ⋙ K) (J ⋙ F) (L ⋙ F)
      (Functor.whiskerRight (eqToHom h) F) = reindex K F L a ≫
    restriction (J ⋙ K) (L ⋙ K) (L ⋙ F) (Functor.whiskerRight (eqToHom h) K) :=
    reindex_eq_transport K F L h a
  change (reindex K F J a ≫ restriction _ _ _ _) ≫ targetMap _ _ _ _ = _
  rw [Category.assoc, ← target_restriction, ← Category.assoc, heq,
    Category.assoc, restriction_comp, ← Functor.whiskerRight_comp]
  rfl

variable (B : E ⥤ Arrow D)

lemma left_reindex : reindex _ _ B (NerveArrowComparison.left K F a) =
    leftAlong K F a (B ⋙ Arrow.leftFunc) (B ⋙ Arrow.rightFunc)
      (Functor.whiskerLeft B Arrow.leftToRight) := by
  change reindex _ _ B (mapTarget _ _ _ _ (reindex K F Arrow.leftFunc a)) = _
  rw [reindex_mapTarget, reindex_reindex]
  rfl

lemma right_reindex : reindex _ _ B (NerveArrowComparison.right K F a) =
    rightAlong K F a (B ⋙ Arrow.leftFunc) (B ⋙ Arrow.rightFunc)
      (Functor.whiskerLeft B Arrow.leftToRight) := by
  change reindex _ _ B (reindex K F Arrow.rightFunc a ≫ restriction _ _ _ _) = _
  rw [reindex_restriction, reindex_reindex]
  rfl

end SerrePositivity.SimplicialModel.NerveArrowComparisonComposition
