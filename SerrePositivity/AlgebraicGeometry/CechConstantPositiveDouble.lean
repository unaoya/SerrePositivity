module

public import SerrePositivity.AlgebraicGeometry.CechConstantCochainComplex

/-!
概要：同じ定数二重複体の正の外次数を残す商。
方針：外零次に明示的な零複体を置き、正次数の各項と微分を保つ。
規約：零複体の各次数は同じ選ばれた零加群。
使われ方：F8の余分な定数基底列を除く短完全列の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type v} [CommRing R] (A : CochainComplex (ModuleCat.{u} R) ℕ)

/-- 外零次は明示的な零複体、正次数は元の同じ複体。 -/
def cechConstantPositiveDoubleTerm : ℕ → CochainComplex (ModuleCat.{u} R) ℕ
  | 0 => HomologicalComplex.zero
  | _ + 1 => A

/-- 正の外次数では元の定数図式の微分を使う。 -/
def cechConstantPositiveDoubleD :
    ∀ n, cechConstantPositiveDoubleTerm A n ⟶ cechConstantPositiveDoubleTerm A (n + 1)
  | 0 => 0
  | n + 1 => (cechConstantCochainComplex A).d (n + 1) (n + 2)

/-- 同じ外微分の二乗は零。 -/
theorem cechConstantPositiveDoubleD_squared (n : ℕ) :
    cechConstantPositiveDoubleD A n ≫ cechConstantPositiveDoubleD A (n + 1) = 0 := by
  cases n with
  | zero => exact zero_comp
  | succ n => exact (cechConstantCochainComplex A).d_comp_d (n + 1) (n + 2) (n + 3)

/-- 同じ定数図式の正の外次数だけを残した二重複体。 -/
def cechConstantPositiveDouble : CochainComplex (CochainComplex (ModuleCat.{u} R) ℕ) ℕ :=
  CochainComplex.of (cechConstantPositiveDoubleTerm A) (cechConstantPositiveDoubleD A)
    (cechConstantPositiveDoubleD_squared A)

/-- 元の定数図式から正の外次数への同じ射影の各成分。 -/
def cechConstantPositiveDoubleProjectionComponent :
    ∀ n, (cechConstantCochainComplex A).X n ⟶ (cechConstantPositiveDouble A).X n
  | 0 => 0
  | _ + 1 => 𝟙 A

set_option backward.isDefEq.respectTransparency false in
/-- 元の定数図式から正の外次数だけを残す同じ射影。 -/
def cechConstantPositiveDoubleProjection :
    cechConstantCochainComplex A ⟶ cechConstantPositiveDouble A :=
  CochainComplex.ofHom (cechConstantPositiveDoubleProjectionComponent A) (by
    intro n
    cases n with
    | zero =>
      change 0 ≫ _ = (cechConstantCochainComplex A).d 0 1 ≫ 𝟙 A
      rw [cechConstantCochainComplex_d, ite_eq_left (show Even 2 by decide),
        zero_comp, zero_comp]
    | succ n =>
      change 𝟙 A ≫ (cechConstantPositiveDouble A).d (n + 1) (n + 2) =
        (cechConstantCochainComplex A).d (n + 1) (n + 2) ≫ 𝟙 A
      have h : (cechConstantPositiveDouble A).d (n + 1) (n + 2) =
          (cechConstantCochainComplex A).d (n + 1) (n + 2) := CochainComplex.of_d _ _ _
      exact (Category.id_comp _).trans (h.trans (Category.comp_id _).symm))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ射影の全ての外次数・縦次数の成分は全射。 -/
theorem cechConstantPositiveDoubleProjection_surjective (n b : ℕ) :
    Function.Surjective (((cechConstantPositiveDoubleProjection A).f n).f b).hom := by
  cases n with
  | zero =>
    haveI : Epi (((cechConstantPositiveDoubleProjection A).f 0).f b) :=
      (isZero_zero (ModuleCat.{u} R)).epi _
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  | succ n =>
    change Function.Surjective (LinearMap.id : A.X b →ₗ[R] A.X b)
    exact Function.surjective_id

end SerrePositivity.AlgebraicGeometry
