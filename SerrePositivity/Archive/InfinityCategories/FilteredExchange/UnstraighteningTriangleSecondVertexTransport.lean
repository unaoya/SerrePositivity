module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.UnstraighteningTriangleVertex

/-!
概要：元の三角形の第二変換の頂点表示だけの変更は、指定全空間比較の値を保持する。
方針：頂点等式を消去し、同じ全二単体と後合成を使う。
規約：三角形・単位表現を選び直さない。使われ方：上面の native 単位表示の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ第二変換の頂点等式による表示変更は、全空間比較の後合成の指定値を保持する。 -/
lemma unstraighteningTriangleVertexIso_postcomp_heq_second_eq {B W : SSet.{u + 1}}
    (F G J : B ⟶ SpaceInfinity.{u})
    (x : (leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (y y' : (leftUnstraighteningTransformationSpace G J) _⦋0⦌)
    (z : (leftUnstraighteningTransformationSpace F J) _⦋0⦌)
    (H : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ (Δ[0] : SSet.{u + 1})) ⟶ SpaceInfinity.{u})
    (hy : y = y')
    (h₀₁ : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const x))
    (h₁₂ : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const y))
    (h₁₂' : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const y'))
    (h₀₂ : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ H =
      coherentTransformationFamilyDiagram (SSet.const z)) (p : leftUnstraightening J ⟶ W) :
    HEq ((unstraighteningTriangleVertexIso F G J x y z H h₀₁ h₁₂ h₀₂).postcomp p)
      ((unstraighteningTriangleVertexIso F G J x y' z H h₀₁ h₁₂' h₀₂).postcomp p) := by
  subst y'
  rfl

end SerrePositivity.InfinityCategories.F2
