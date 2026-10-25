module
public import SerrePositivity.DifferentialGraded.Presentation.CategorySigmaInclusion
public import SerrePositivity.DifferentialGraded.Presentation.CategorySigmaDesc
/-!
概要：非連結和からの共通評価を各成分へ制限すると元の dg 関手に厳密に一致する。
方針：同一成分の二つの等式移送が互いに逆であることを全 Hom で検証する。
規約：対象と全次数の作用を比較し、ホモトピー圏だけの一致で代用しない。
使われ方：出発提示の同時精密化と元の arrow の延長比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R] (B J : Type u) (X : J → Type u)
  (c : ∀ j, DGCategoryPresentationData R B (X j)) (D : Type v) [DGCategory R D]
  (F : ∀ j, letI := (c j).enrichment R B (X j); DGFunctor R (X j) D)
namespace DGCategoryPresentationData

lemma sigmaDescMap_same (j : J) (x y : X j) :
    letI (j : J) := (c j).enrichment R B (X j)
    sigmaDescMap R B J X c D F ⟨j, x⟩ ⟨j, y⟩ =
      eqToHom (sigmaHom_value_same R B J X c j x y) ≫ (F j).map x y := by
  classical
  dsimp only [sigmaDescMap]
  split_ifs <;> first | rfl | contradiction

lemma sigmaInclusion_comp_sigmaDesc (j : J) :
    letI (j : J) := (c j).enrichment R B (X j)
    letI := (sigma R B J X c).enrichment R B (Sigma X)
    (sigmaInclusion R B J X c j).comp (sigmaDesc R B J X c D F) = F j := by
  letI (j : J) := (c j).enrichment R B (X j)
  letI := (sigma R B J X c).enrichment R B (Sigma X)
  apply EnrichedFunctor.ext (Complex R)
    (F := (sigmaInclusion R B J X c j).comp (sigmaDesc R B J X c D F))
    (G := F j) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]
  change sigmaInclusionMap R B J X c j x y ≫
    sigmaDescMap R B J X c D F ⟨j, x⟩ ⟨j, y⟩ = (F j).map x y
  rw [sigmaDescMap_same]
  simp only [sigmaInclusionMap, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]

end DGCategoryPresentationData
end SerrePositivity.DifferentialGraded
