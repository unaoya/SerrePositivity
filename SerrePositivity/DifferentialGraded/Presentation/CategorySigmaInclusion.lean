module
public import SerrePositivity.DifferentialGraded.Presentation.CategorySigma
public import SerrePositivity.DifferentialGraded.Functor.Basic
/-!
概要：非連結和の各成分を、全 Hom の同型を保持して包含する。
方針：同一成分の Hom 提示の等式で恒等鎖写像を移送し、三法則を抽象移送する。
規約：異成分の Hom を埋める追加データは要求しない。
使われ方：異なる出発提示の seed を共通の出発圏へ延長する包含。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (R : Type u) [CommRing R] (B J : Type u) (X : J → Type u)
  (c : ∀ j, DGCategoryPresentationData R B (X j))
namespace DGCategoryPresentationData

def sigmaInclusionMap (j : J) (x y : X j) :
    ((c j).hom x y).value R B ⟶ (sigmaHom R B J X c ⟨j, x⟩ ⟨j, y⟩).value R B :=
  eqToHom (sigmaHom_value_same R B J X c j x y).symm

lemma sigmaInclusionMap_heq (j : J) (x y : X j) :
    HEq (sigmaInclusionMap R B J X c j x y) (𝟙 (((c j).hom x y).value R B)) := by
  unfold sigmaInclusionMap
  exact eqToHom_heq_id_dom _ _ _

def sigmaInclusion (j : J) :
    letI := (c j).enrichment R B (X j)
    letI := (sigma R B J X c).enrichment R B (Sigma X)
    DGFunctor R (X j) (Sigma X) := by
  letI := (c j).enrichment R B (X j)
  letI := (sigma R B J X c).enrichment R B (Sigma X)
  exact {
    obj := Sigma.mk j
    map := sigmaInclusionMap R B J X c j
    map_id x := enrichedFunctorUnitLaw_of_heq rfl
      (sigmaHom_value_same R B J X c j x x)
      _ _ _ _ _ _ (HEq.rfl) (sigmaUnit_heq R B J X c j x)
      (sigmaInclusionMap_heq R B J X c j x x) (Category.comp_id _)
    map_comp x y z := enrichedFunctorCompLaw_of_heq rfl rfl rfl
      (sigmaHom_value_same R B J X c j x y)
      (sigmaHom_value_same R B J X c j y z)
      (sigmaHom_value_same R B J X c j x z)
      _ _ _ _ _ _ _ _ _ _ (HEq.rfl) (sigmaComp_heq R B J X c j x y z)
      (sigmaInclusionMap_heq R B J X c j x y)
      (sigmaInclusionMap_heq R B J X c j y z)
      (sigmaInclusionMap_heq R B J X c j x z)
      (by
        change (c j).comp x y z ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ (c j).comp x y z
        simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]) }

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
