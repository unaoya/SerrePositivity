module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UnstraighteningMappingTrianglePrism

/-!
概要：元の三角形の長辺 prism は三辺の族の厳密な表示変更で保たれる。
方針：三辺の射の等式を消去し、同じ全三角形と面の証明の一意性へ戻す。
規約：長辺の持ち上げを再選択しない。使われ方：定値区間表示の元の長辺への照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B K : SSet.{u + 1}} (F G J : B ⟶ SpaceInfinity.{u})
  (a a' : K ⟶ leftUnstraighteningTransformationSpace F G)
  (b b' : K ⟶ leftUnstraighteningTransformationSpace G J)
  (c c' : K ⟶ leftUnstraighteningTransformationSpace F J)
  (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ K) ⟶ SpaceInfinity.{u})
  (ha : a = a') (hb : b = b') (hc : c = c')
  (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
    coherentTransformationFamilyDiagram a)
  (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
    coherentTransformationFamilyDiagram b)
  (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
    coherentTransformationFamilyDiagram c)
  (h₀₁' : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ K)) ≫ H =
    coherentTransformationFamilyDiagram a')
  (h₁₂' : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ K)) ≫ H =
    coherentTransformationFamilyDiagram b')
  (h₀₂' : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ K)) ≫ H =
    coherentTransformationFamilyDiagram c')

include ha hb hc in
/-- 三辺の全族が同じなら、同じ全三角形から得た指定長辺 prism も厳密に同じ。 -/
lemma unstraighteningMappingTriangleLongWitness_leftPrism_eq_of_families :
    (unstraighteningMappingTriangleLongWitness F G J a b c H h₀₁ h₁₂ h₀₂).leftPrism =
      (unstraighteningMappingTriangleLongWitness F G J a' b' c' H h₀₁' h₁₂' h₀₂').leftPrism := by
  subst a' b' c'
  rfl

end SerrePositivity.InfinityCategories.F2
