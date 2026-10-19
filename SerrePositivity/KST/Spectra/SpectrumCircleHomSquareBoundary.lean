module

public import SerrePositivity.KST.Spectra.SpectrumNativeZeroTriangleTrace

/-!
概要：元の円評価三単体の Hom 正方形の二つの終辺は定値である。
方針：元の参照面・退化面の定値性と、最初・最後の辺の定値な Hom 経路を合成する。
規約：元の Hom 正方形を保持。使われ方：生成 loop と companion 経路の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open CoherentPathCoordinates

private lemma constant_pair {A B T : SSet.{u}} (a : A _⦋0⦌) (b : B _⦋0⦌) :
    lift (SSet.const (X := T) a) (SSet.const b) = SSet.const (Y := A ⊗ B) (a, b) := rfl

/-- 元の Hom 正方形の第一座標一の辺は、元の Hom 内の定値経路。 -/
lemma circleEvaluationHomSquare_includeFirst_constant (z : Sp.{u} _⦋0⦌) :
    ∃ y, lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
      (𝟙 (Δ[1] : SSet.{u})) ≫ circleEvaluationHomSquare z = SSet.const y := by
  rw [circleEvaluationHomSquare_includeFirst]
  obtain ⟨y, hy⟩ := circleEvaluationReferenceTrace_constant z
  rw [hy]
  unfold tetrahedronInitialTrace
  rw [constantPathParameter_eq_const, SSet.const_comp, constant_pair, SSet.const_comp]
  exact ⟨_, rfl⟩

/-- 元の Hom 正方形の第二座標一の辺も、元の Hom 内の定値経路。 -/
lemma circleEvaluationHomSquare_includeSecond_constant (z : Sp.{u} _⦋0⦌) :
    ∃ y, lift (𝟙 (Δ[1] : SSet.{u}))
      (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫
        circleEvaluationHomSquare z = SSet.const y := by
  rw [circleEvaluationHomSquare_includeSecond]
  obtain ⟨y, hy⟩ := circleEvaluationDegenerateTrace_constant z
  rw [hy]
  unfold tetrahedronFinalTrace
  rw [constantPathParameter_eq_const, SSet.const_comp, constant_pair, SSet.const_comp]
  exact ⟨_, rfl⟩

end SerrePositivity.KST.Spectra.OmegaSpectrum
