module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowBoundary
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowCochain
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.StandardRowBoundary
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.DirectSumTotal
import all Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# 標準列の微分と同じ単体境界の cochain 等式

## 概要
実現の次数 -(n+1) の標準列の微分を、元の交代面微分と次数 -n の列の合成に同定する。

## 方針
全行の成分公式と同じ延長の次数同型の微分公式を合成する。

## 規約
非有界の内部次数と元の面の符号を保つ。

## 使われ方
HA 1.2.4。既存 coherent bar の theta に対する比較射の閉性。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex CochainComplex HomComplex AlgebraicTopology
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
variable (A : Type u) [CommRing A]

/-- 元の標準列の微分は、同じ交代面微分の後の一つ下の標準列。 -/
theorem standardRowCochain_δ (X : SimplicialObject (Complex A)) (n : ℕ) :
    δ (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1) (standardRowCochain A X (n + 1)) =
      (Cochain.ofHom ((AlternatingFaceMapComplex.obj X).d (n + 1) n)).comp
        (standardRowCochain A X n) (by omega) := by
  apply Cochain.ext
  intro p q hpq
  have hq : q = (p + -((n + 1 : ℕ) : ℤ)) + 1 := by omega
  cases hq
  rw [Cochain.comp_v _ _ (by omega) p p _ (by omega) (by omega),
    standardRowCochain_v]
  simp only [Cochain.ofHom_v]
  have hd := doubleComplexRow_d A X n
  have hdeg : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
  have h := standardRowCochain_δ_v A X (n + 1) p
  erw [h]
  let K := (doubleComplexFunctor A).obj X
  let i₁ : X.obj (Opposite.op (SimplexCategory.mk (n + 1))) ⟶ K.X (-((n + 1 : ℕ) : ℤ)) :=
    (doubleComplexRowIso A X (n + 1)).inv
  let i₀ : X.obj (Opposite.op (SimplexCategory.mk n)) ⟶ K.X (-(n : ℤ)) :=
    (doubleComplexRowIso A X n).inv
  let d : X.obj (Opposite.op (SimplexCategory.mk (n + 1))) ⟶
      X.obj (Opposite.op (SimplexCategory.mk n)) :=
    (AlternatingFaceMapComplex.obj X).d (n + 1) n
  have hd' : i₁ ≫ K.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) = d ≫ i₀ := hd
  have h' : i₁.f p ≫ (K.d (-((n + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ) + 1)).f p ≫
      K.ιTotalOrZero (.up ℤ) (-((n + 1 : ℕ) : ℤ) + 1) p (p + -((n + 1 : ℕ) : ℤ) + 1) =
      d.f p ≫ i₀.f p ≫
      K.ιTotalOrZero (.up ℤ) (-(n : ℤ)) p (p + -((n + 1 : ℕ) : ℤ) + 1) := by
    rw [hdeg]
    exact (congrArg (fun f => f.f p ≫ K.ιTotalOrZero (.up ℤ) (-(n : ℤ)) p
      (p + -((n + 1 : ℕ) : ℤ) + 1)) hd').trans (Category.assoc _ _ _)
  have h₁ := K.ιTotalOrZero_eq (.up ℤ) (-((n + 1 : ℕ) : ℤ) + 1) p
    (p + -((n + 1 : ℕ) : ℤ) + 1) (by dsimp; omega)
  have h₀ := K.ιTotalOrZero_eq (.up ℤ) (-(n : ℤ)) p
    (p + -((n + 1 : ℕ) : ℤ) + 1) (by dsimp; omega)
  rw [h₁, h₀] at h'
  exact h'

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
