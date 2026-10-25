module
public import SerrePositivity.DifferentialGraded.Presentation.CategorySigma
public import SerrePositivity.DifferentialGraded.Functor.Basic
/-!
概要：各出発提示からの dg 関手を非連結和からの一つの関手へまとめる。
方針：同じ成分の鎖写像を等式移送し、異成分には零鎖写像を使う。
規約：元の成分内の Hom 作用を保持し、標的の Small 性を要求しない。
使われ方：異なる arrow の二項・可算直和に必要な共通評価関手。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits MonoidalCategory
variable (R : Type u) [CommRing R] (B J : Type u) (X : J → Type u)
  (c : ∀ j, DGCategoryPresentationData R B (X j)) (D : Type v) [DGCategory R D]
variable (F : ∀ j, letI := (c j).enrichment R B (X j); DGFunctor R (X j) D)
namespace DGCategoryPresentationData

def sigmaDescMap (x y : Sigma X) :
    letI (j : J) := (c j).enrichment R B (X j)
    (sigmaHom R B J X c x y).value R B ⟶ (F x.1).obj x.2 ⟶[Complex R] (F y.1).obj y.2 := by
  letI (j : J) := (c j).enrichment R B (X j)
  classical
  rcases x with ⟨j, x⟩
  rcases y with ⟨k, y⟩
  by_cases h : j = k
  · subst k
    exact eqToHom (sigmaHom_value_same R B J X c j x y) ≫ (F j).map x y
  · exact 0

lemma sigmaDescMap_heq (j : J) (x y : X j) :
    letI (j : J) := (c j).enrichment R B (X j)
    HEq (sigmaDescMap R B J X c D F ⟨j, x⟩ ⟨j, y⟩) ((F j).map x y) := by
  letI (j : J) := (c j).enrichment R B (X j)
  classical
  dsimp only [sigmaDescMap]
  split_ifs <;> first | exact eqToHom_comp_heq _ _ | contradiction

def sigmaDesc :
    letI (j : J) := (c j).enrichment R B (X j)
    letI := (sigma R B J X c).enrichment R B (Sigma X)
    DGFunctor R (Sigma X) D := by
  letI (j : J) := (c j).enrichment R B (X j)
  letI := (sigma R B J X c).enrichment R B (Sigma X)
  exact {
    obj x := (F x.1).obj x.2
    map := sigmaDescMap R B J X c D F
    map_id x := by
      rcases x with ⟨j, x⟩
      exact enrichedFunctorUnitLaw_of_heq
        (sigmaHom_value_same R B J X c j x x) rfl
        _ _ _ _ _ _ (sigmaUnit_heq R B J X c j x) (HEq.rfl)
        (sigmaDescMap_heq R B J X c D F j x x) ((F j).map_id x)
    map_comp x y z := by
      rcases x with ⟨j, x⟩
      rcases y with ⟨k, y⟩
      rcases z with ⟨l, z⟩
      by_cases h₁ : j = k
      · subst k
        by_cases h₂ : j = l
        · subst l
          exact enrichedFunctorCompLaw_of_heq
            (sigmaHom_value_same R B J X c j x y)
            (sigmaHom_value_same R B J X c j y z)
            (sigmaHom_value_same R B J X c j x z) rfl rfl rfl
            _ _ _ _ _ _ _ _ _ _ (sigmaComp_heq R B J X c j x y z) (HEq.rfl)
            (sigmaDescMap_heq R B J X c D F j x y)
            (sigmaDescMap_heq R B J X c D F j y z)
            (sigmaDescMap_heq R B J X c D F j x z) ((F j).map_comp x y z)
        · exact ((tensorLeft ((sigmaHom R B J X c ⟨j, x⟩ ⟨j, y⟩).value R B)).map_isZero
            (sigmaHom_isZero_ne R B J X c h₂ y z)).eq_of_src _ _
      · exact ((tensorRight ((sigmaHom R B J X c ⟨k, y⟩ ⟨l, z⟩).value R B)).map_isZero
          (sigmaHom_isZero_ne R B J X c h₁ x y)).eq_of_src _ _ }

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
