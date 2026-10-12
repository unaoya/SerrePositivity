module

public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.CategoryTheory.IteratedCone

/-! # 任意の複体の Koszul 塔と抽象的な反復錐

有界性・自由性・射影性を要求せず、実際の Koszul 複体をホモトピー圏の
スカラー錐の列にする。消去スカラーの保存は共通の反復錐定理を適用する。
-/

@[expose] public section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Pretriangulated
variable {R : Type u} [CommRing R]

/-- 任意の複体に対する Koszul 錐の第 k 段。 -/
noncomputable def homotopyKoszulObj (x : ℕ → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (k : ℕ) :=
  (homotopyQuot R).obj (koszulComplexOn (fun j : Fin k ↦ x j) P)

/-- 任意の複体の Koszul 錐を与える完全三角形。 -/
noncomputable def homotopyKoszulTriangle (x : ℕ → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (k : ℕ) :=
  CochainComplex.mappingCone.triangleh
    (smulId (x k) (koszulComplexOn (fun j : Fin k ↦ x j) P))

/-- 実際の Koszul 塔の三角形は、指定スカラーの錐の三角形である。 -/
lemma homotopyKoszulTriangle_mk_distinguished (x : ℕ → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (k : ℕ) :
    Triangle.mk (x k • 𝟙 (homotopyKoszulObj x P k))
      (homotopyKoszulTriangle x P k).mor₂ (homotopyKoszulTriangle x P k).mor₃ ∈ distTriang _ := by
  have he : (homotopyKoszulTriangle x P k).mor₁ =
      x k • 𝟙 (homotopyKoszulObj x P k) := by
    change (homotopyQuot R).map (x k • 𝟙 _) = _
    exact ((homotopyQuot R).map_smul (x k) (𝟙 _)).trans
      (congrArg (fun f ↦ x k • f) ((homotopyQuot R).map_id _))
  rw [← he]
  exact HomotopyCategory.mappingCone_triangleh_distinguished _

/-- 初項を消すスカラーは Koszul 構成後も指数を増やさずに零作用する。 -/
lemma koszulComplexOn_smul_zero {e : ℕ} (x : Fin e → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hx : ∀ j, x j • 𝟙 ((homotopyQuot R).obj P) = 0)
    (a : R) (ha : a • 𝟙 ((homotopyQuot R).obj P) = 0) :
    a • 𝟙 ((homotopyQuot R).obj (koszulComplexOn x P)) = 0 := by
  let y : ℕ → R := fun j ↦ if h : j < e then x ⟨j, h⟩ else 0
  have hy : (fun j : Fin e ↦ y j) = x := by funext j; simp [y, j.isLt]
  have h := iteratedScalarCone_smul_zero_of_smul_zero
    (homotopyKoszulObj y P) (fun k ↦ (homotopyKoszulTriangle y P k).mor₂)
    (fun k ↦ (homotopyKoszulTriangle y P k).mor₃) e y
    (fun k _ ↦ homotopyKoszulTriangle_mk_distinguished y P k)
    (fun j hj ↦ by
      change y j • 𝟙 ((homotopyQuot R).obj P) = 0
      simpa only [y, dite_eq_left hj] using hx ⟨j, hj⟩)
    a ha e le_rfl
  change a • 𝟙 ((homotopyQuot R).obj (koszulComplexOn (fun j : Fin e ↦ y j) P)) = 0 at h
  rw [hy] at h
  exact h

end SerrePositivity
