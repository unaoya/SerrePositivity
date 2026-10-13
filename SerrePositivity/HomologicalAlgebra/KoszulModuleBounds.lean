module

public import SerrePositivity.HomologicalAlgebra.KoszulScalarControl

/-! # 任意の係数加群の Koszul 複体の次数の範囲

e個の元のKoszul構成は、係数加群の有限性に関係なく -e,…,0 次に集中する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R]

/-- 係数加群のKoszul複体は正次数に項を持たない。 -/
theorem koszulModuleFunctor_isZero_X_of_pos : ∀ {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R) (q : ℤ), 0 < q → IsZero (((koszulModuleFunctor z).obj M).X q)
  | 0, z, M, q, hq => HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M q (by omega)
  | e + 1, z, M, q, hq => by
    change IsZero ((CochainComplex.mappingCone
      (smulId (z (Fin.last e)) ((koszulModuleFunctor (Fin.init z)).obj M))).X q)
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨koszulModuleFunctor_isZero_X_of_pos (Fin.init z) M (q + 1) (by omega),
      koszulModuleFunctor_isZero_X_of_pos (Fin.init z) M q hq⟩

/-- 係数加群のKoszul複体は列の長さの負より小さい次数に項を持たない。 -/
theorem koszulModuleFunctor_isZero_X_of_lt : ∀ {e : ℕ} (z : Fin e → R)
    (M : ModuleCat.{u} R) (q : ℤ), q < -(e : ℤ) → IsZero (((koszulModuleFunctor z).obj M).X q)
  | 0, z, M, q, hq => HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M q (by omega)
  | e + 1, z, M, q, hq => by
    change IsZero ((CochainComplex.mappingCone
      (smulId (z (Fin.last e)) ((koszulModuleFunctor (Fin.init z)).obj M))).X q)
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨koszulModuleFunctor_isZero_X_of_lt (Fin.init z) M (q + 1) (by omega),
      koszulModuleFunctor_isZero_X_of_lt (Fin.init z) M q (by omega)⟩

/-- 任意の係数加群のKoszul複体の有界性を、Euler評価の仮定として供給する。 -/
theorem koszulModuleFunctor_bounded {e : ℕ} (z : Fin e → R) (M : ModuleCat.{u} R) :
    ∃ a b : ℤ, ∀ q, (q < a ∨ b < q) → IsZero (((koszulModuleFunctor z).obj M).X q) :=
  ⟨-(e : ℤ), 0, fun q hq ↦ hq.elim
    (koszulModuleFunctor_isZero_X_of_lt z M q) (koszulModuleFunctor_isZero_X_of_pos z M q)⟩

end SerrePositivity
