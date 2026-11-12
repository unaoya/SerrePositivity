module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.UnstraighteningTriangleComposition
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoComponentTransport

/-!
概要：同じ全三角形の辺の族を等しい表示へ変えても、指定比較の成分を保持する。
方針：三辺の族の等式を消去し、元の二単体と同じ比較を使う。
規約：充填や比較を再選択しない。使われ方：下面の区間族表示との照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 三辺の同じ全族への等式輸送は、元の全三角形比較の同じ点の値を保持する。 -/
lemma unstraighteningMappingTriangleIso_app_heq_of_family_eq {B K : SSet.{u + 1}}
    [Quasicategory K]
    (F G J : B ⟶ SpaceInfinity.{u})
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
      coherentTransformationFamilyDiagram c') (x : K _⦋0⦌) :
    HEq ((unstraighteningMappingTriangleIso F G J a b c H h₀₁ h₁₂ h₀₂).app x)
      ((unstraighteningMappingTriangleIso F G J a' b' c' H h₀₁' h₁₂' h₀₂').app x) := by
  subst a' b' c'
  rfl

end SerrePositivity.InfinityCategories.F2
