module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Functoriality.FunctorTriangleOfFamily
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-! # 三つの標準合成面を保つ四面体の族

概要：正規化の前後面と終側の合成面を、全パラメーターで四面体に貼る。
方針：三面を関手単体集合の内角 Λ[3,2] へ貼り、既存の quasicategory 充填を使う。
規約：三つの指定面を厳密に回収し、残る面だけを選ぶ。
使われ方：共有面・側面を含む正規化比較を、単なる二変形から区別して保持する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial

/-- 概要：標準単体の全パラメーター族を関手単体集合へ移す。
方針：因子を交換して curry する。規約：元の族をそのまま使う。
使われ方：四面体の三つの既知面を貼る。 -/
def dgGluingSimplexFamilyCurry {K X : SSet.{u}} {n : ℕ}
    (f : (Δ[n] : SSet.{u}) ⊗ K ⟶ X) : Δ[n] ⟶ (ihom K).obj X :=
  curry ((β_ K (Δ[n] : SSet.{u})).hom ≫ f)

lemma dgGluingSimplexFamilyCurry_face {K X : SSet.{u}} {n : ℕ}
    (f : (Δ[n + 1] : SSet.{u}) ⊗ K ⟶ X) (i : Fin (n + 2)) :
    stdSimplex.δ i ≫ dgGluingSimplexFamilyCurry f =
      dgGluingSimplexFamilyCurry ((stdSimplex.δ i ▷ K) ≫ f) := by
  apply uncurry_injective
  rw [dgGluingSimplexFamilyCurry, uncurry_natural_left, uncurry_curry,
    dgGluingSimplexFamilyCurry, uncurry_curry]
  rfl

lemma dgGluingTetrahedronFamily_exists {K X : SSet.{u}} [Quasicategory X]
    (f₀ f₁ f₃ : (Δ[2] : SSet.{u}) ⊗ K ⟶ X)
    (h₀₂ : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ f₁ =
      (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ f₃)
    (h₁₂ : (stdSimplex.δ (2 : Fin 3) ▷ K) ≫ f₀ =
      (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ f₃)
    (h₂₃ : (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ f₀ =
      (stdSimplex.δ (0 : Fin 3) ▷ K) ≫ f₁) :
    ∃ V : (Δ[3] : SSet.{u}) ⊗ K ⟶ X,
      (stdSimplex.δ (0 : Fin 4) ▷ K) ≫ V = f₀ ∧
      (stdSimplex.δ (1 : Fin 4) ▷ K) ≫ V = f₁ ∧
      (stdSimplex.δ (3 : Fin 4) ▷ K) ≫ V = f₃ := by
  let a := horn₃₂.desc (dgGluingSimplexFamilyCurry f₀)
    (dgGluingSimplexFamilyCurry f₁) (dgGluingSimplexFamilyCurry f₃)
    (by rw [dgGluingSimplexFamilyCurry_face, dgGluingSimplexFamilyCurry_face, h₀₂])
    (by rw [dgGluingSimplexFamilyCurry_face, dgGluingSimplexFamilyCurry_face, h₁₂])
    (by rw [dgGluingSimplexFamilyCurry_face, dgGluingSimplexFamilyCurry_face, h₂₃])
  obtain ⟨v, hv⟩ := Quasicategory.hornFilling (S := (ihom K).obj X)
    (i := (2 : Fin 4)) (by decide) (by decide) a
  have h₀ : stdSimplex.δ (0 : Fin 4) ≫ v = dgGluingSimplexFamilyCurry f₀ := by
    have he := congrArg (fun z => horn₃₂.ι₀ ≫ z) hv
    simpa only [a, horn₃₂.ι₀_desc, ← Category.assoc, horn.ι_ι] using he.symm
  have h₁ : stdSimplex.δ (1 : Fin 4) ≫ v = dgGluingSimplexFamilyCurry f₁ := by
    have he := congrArg (fun z => horn₃₂.ι₁ ≫ z) hv
    simpa only [a, horn₃₂.ι₁_desc, ← Category.assoc, horn.ι_ι] using he.symm
  have h₃ : stdSimplex.δ (3 : Fin 4) ≫ v = dgGluingSimplexFamilyCurry f₃ := by
    have he := congrArg (fun z => horn₃₂.ι₃ ≫ z) hv
    simpa only [a, horn₃₂.ι₃_desc, ← Category.assoc, horn.ι_ι] using he.symm
  refine ⟨(β_ (Δ[3] : SSet.{u}) K).hom ≫ uncurry v, ?_, ?_, ?_⟩
  all_goals
    rw [BraidedCategory.braiding_naturality_left_assoc, ← uncurry_natural_left]
  · rw [h₀, dgGluingSimplexFamilyCurry, uncurry_curry, SymmetricCategory.symmetry_assoc]
  · rw [h₁, dgGluingSimplexFamilyCurry, uncurry_curry, SymmetricCategory.symmetry_assoc]
  · rw [h₃, dgGluingSimplexFamilyCurry, uncurry_curry, SymmetricCategory.symmetry_assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
