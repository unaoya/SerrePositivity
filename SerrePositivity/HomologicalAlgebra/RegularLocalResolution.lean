module

public import SerrePositivity.HomologicalAlgebra.FiniteFreeResolution
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic

/-! # 正則局所環上の有限自由分解

証明済みの正則生成列から、一般の分解構成を適用する。
交点重複度の消滅定理などの引用には依存しない。
-/

public section
universe u
open CategoryTheory
namespace SerrePositivity
variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- 正則局所環上の有界有限自由分解の存在。極大イデアルの正則生成列を選び、
一般定理から自然数添字の有限自由分解を構成し、整数添字へ移す。
正則パラメータの正則性を含めて証明済み。 -/
theorem regularResolution (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ F : CochainComplex (ModuleCat.{u} R) ℤ,
      Nonempty (IsResolutionOf F (ModuleCat.of R M)) ∧
      (∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → CategoryTheory.Limits.IsZero (F.X i)) ∧
      (∀ i, Module.Free R (F.X i)) ∧ (∀ i, Module.Finite R (F.X i)) := by
  obtain ⟨rs, hreg, hgen, _⟩ := exists_regular_generators R
  obtain ⟨P, hb, hfree, hfinite⟩ :=
    exists_finite_free_resolution_of_regular_generators rs hreg hgen (ModuleCat.of R M)
  obtain ⟨F, hF, hbound, hfree, hfinite⟩ :=
    bounded_finite_free_cochain_of_projectiveResolution P rs.length hb hfree hfinite
  exact ⟨F, hF, ⟨-(rs.length : ℤ), 0, hbound⟩, hfree, hfinite⟩

end SerrePositivity
