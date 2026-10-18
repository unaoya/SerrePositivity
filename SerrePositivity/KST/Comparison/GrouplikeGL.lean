module

public import SerrePositivity.KST.Comparison.MonoidComponents

/-!
# ĜL の一般の群状性界面への接続

概要：ĜL_r の成分群の計算を一般の群状単体的モノイドの条件へ接続する。
方針：成分行列への全単射が標準の誘導乗法を保つことを零次単体で確認する。
規約：π₀ のモノイドは零次の商から作ったものを用いる。KST 式 (2.2)。
使われ方：Segal 1974 Proposition 1.5 の群状性の実際の供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.Comparison

open CategoryTheory SSet

/--
概要：π₀ で可逆な行列の単体的モノイドは一般の意味でも群状である。
方針：誘導乗法を保つ成分行列の全単射から各成分の二側逆を作る。
規約：各次数の行列の可逆性は要求しない。KST 式 (2.2)、Segal 1974 Proposition 1.5。
使われ方：ĜL_r の bar が delooping を与えることの群状性の仮定。
-/
theorem hatGL_isGrouplike (A : SimplicialObject RingCat.{u}) (r : ℕ) :
    SimplicialMonoid.IsGrouplike (hatGLMonoidObject A r) := by
  let M := hatGLMonoidObject A r
  let := SimplicialMonoid.componentsMonoid M
  let : One (π₀ (monoidSpace M)) := (SimplicialMonoid.componentsMonoid M).toOne
  let : Mul (π₀ (monoidSpace M)) := (SimplicialMonoid.componentsMonoid M).toMul
  let e : π₀ (monoidSpace M) ≃ (Matrix (Fin r) (Fin r) (π₀ (ringSpace A)))ˣ :=
    hatGLComponentsEquiv A r
  have hm (a b : π₀ (monoidSpace M)) : e (a * b) = e a * e b := by
    induction a using π₀.rec with | mk a => ?_
    induction b using π₀.rec with | mk b => ?_
    exact hatGLVertexUnit_mul A r a b
  have h1 : e 1 = 1 := by
    change hatGLVertexUnit A r (1 : hatGLSubmonoid A r 0) = 1
    apply Units.ext
    change (IsUnit.unit ((1 : hatGLSubmonoid A r 0).property)).val = 1
    rw [IsUnit.unit_spec]
    exact (matrixToComponents A r 0).map_one
  intro a
  refine ⟨⟨a, e.symm ((e a)⁻¹), ?_, ?_⟩, rfl⟩
  · apply e.injective
    rw [hm, e.apply_symm_apply]
    exact (mul_inv_cancel (e a)).trans h1.symm
  · apply e.injective
    rw [hm, e.apply_symm_apply]
    exact (inv_mul_cancel (e a)).trans h1.symm

end SerrePositivity.KST.Comparison
