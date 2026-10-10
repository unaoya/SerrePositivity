module

public import SerrePositivity.CategoryTheory.TriangleBiproduct

/-! # 自明な三角形を加えた完全三角形 -/

@[expose] public section

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Preadditive
open scoped ZeroObject

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

noncomputable section

@[simps!]
def triangleAddTarget (T : Triangle C) (B : C) : Triangle C :=
  Triangle.mk (T.mor₁ ≫ (biprod.inl : T.obj₂ ⟶ T.obj₂ ⊞ B))
    (biprod.map T.mor₂ (𝟙 B)) (biprod.fst ≫ T.mor₃)

lemma triangleAddTarget_distinguished (T : Triangle C) (hT : T ∈ distTriang C) (B : C) :
    triangleAddTarget T B ∈ distTriang C := by
  let U := Triangle.mk (0 : 0 ⟶ B) (𝟙 B) 0
  refine isomorphic_distinguished _
    (triangleBiproduct_distinguished T U hT (contractible_distinguished₁ B)) _ ?_
  refine Triangle.isoMk _ _ (isoBiprodZero (isZero_zero C)) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [triangleAddTarget, triangleBiproduct, U]
  · simp [triangleAddTarget, triangleBiproduct, U]
  · dsimp [triangleAddTarget, triangleBiproduct, U]
    apply biprod.hom_ext'
    all_goals simp

@[simps!]
def triangleAddSource (T : Triangle C) (A : C) : Triangle C :=
  Triangle.mk ((biprod.fst : T.obj₁ ⊞ A ⟶ T.obj₁) ≫ T.mor₁)
    (T.mor₂ ≫ biprod.inl)
    (biprod.desc (T.mor₃ ≫ (shiftFunctor C (1 : ℤ)).map biprod.inl)
      ((shiftFunctor C (1 : ℤ)).map biprod.inr))

lemma triangleAddSource_distinguished (T : Triangle C) (hT : T ∈ distTriang C) (A : C) :
    triangleAddSource T A ∈ distTriang C := by
  let U := Triangle.mk (0 : A ⟶ 0) 0 (𝟙 (A⟦(1 : ℤ)⟧))
  refine isomorphic_distinguished _
    (triangleBiproduct_distinguished T U hT (contractible_distinguished₂ A)) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (isoBiprodZero (isZero_zero C)) (Iso.refl _)
    ?_ ?_ ?_
  · dsimp [triangleAddSource, triangleBiproduct, U]
    apply biprod.hom_ext'
    all_goals simp
  · simp [triangleAddSource, triangleBiproduct, U]
  · simp [triangleAddSource, triangleBiproduct, U]

/-- 両端の対象を直和で拡大し、錐に自明な因子を加えた三角形。 -/
@[simps!]
def paddedTriangle (T : Triangle C) (A B : C) : Triangle C :=
  triangleAddSource (triangleAddTarget T B) A

lemma paddedTriangle_distinguished (T : Triangle C) (hT : T ∈ distTriang C) (A B : C) :
    paddedTriangle T A B ∈ distTriang C :=
  triangleAddSource_distinguished _ (triangleAddTarget_distinguished T hT B) A

end

end SerrePositivity
