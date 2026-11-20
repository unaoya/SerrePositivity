module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.UnitMinorPresentationEquiv
public import SerrePositivity.AlgebraicGeometry.LocalMinorPivot
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の小行列式条件からの局所環上の自由性判定。
方針：実際の単元ピボットを選び、次次数の消滅から核をピボット列で生成する。
規約：選んだ完全な関係式行列について証明し、表示独立な Fitting イデアルは仮定しない。
使われ方：平坦化で局所的な生成元数と自由性を小行列式から導く。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：局所環で小行列式イデアルが単位、次次数が零なら、対象はピボット外の成分と実際に同型。
方針：単位イデアルから単射な単元ピボットを選び、次次数の消滅による補成分の同型を構成する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、全関係式が核を生成することを明示する。
使われ方：小行列式条件から局所自由なモデルを実際に選ぶ。
-/
theorem exists_complement_equiv_of_unit_minorIdeal
    {R M m n : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    (H : Matrix m n R) (k : ℕ) (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q)
    (hunit : matrixMinorIdeal H k = ⊤) (hzero : matrixMinorIdeal H (k + 1) = ⊥) :
    ∃ r : Fin k → m, Function.Injective r ∧
      Nonempty (({i : m // i ∉ Set.range r} → R) ≃ₗ[R] M) := by
  classical
  have hI : matrixMinorIdeal H k = Ideal.span {(1 : R)} := by simpa using hunit
  obtain ⟨r, c, u, hr, _, hdet⟩ := exists_injective_minor_unit_multiple H k 1 isRegular_one hI
  have hAunit : IsUnit (H.submatrix r c).det := by
    rw [hdet, one_mul]
    exact u.isUnit
  let : Invertible (H.submatrix r c) :=
    Classical.choice (((H.submatrix r c).isUnit_iff_isUnit_det.mpr hAunit).nonempty_invertible)
  exact ⟨r, hr, ⟨unitMinorPresentationComplementEquiv H r hr c q hq hH hzero⟩⟩

/--
概要：有限自由表示の k 次小行列式イデアルが単位、次次数が零なら、対象は階数 N-k の自由加群。
方針：ピボット外の自由加群との実同型を作り、行分解の濃度で階数を計算する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、N は元の生成元数、関係式の個数は有限とは限らない。
使われ方：有限型の純変換が局所自由になるための小行列式判定。
-/
theorem free_and_finrank_of_unit_minorIdeal
    {R M m n : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Fintype m] (H : Matrix m n R) (k : ℕ)
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q)
    (hunit : matrixMinorIdeal H k = ⊤) (hzero : matrixMinorIdeal H (k + 1) = ⊥) :
    Module.Free R M ∧ Module.finrank R M = Fintype.card m - k := by
  classical
  obtain ⟨r, hr, ⟨e⟩⟩ := exists_complement_equiv_of_unit_minorIdeal H k q hq hH hunit hzero
  let κ := {i : m // i ∉ Set.range r}
  let : Fintype κ := Fintype.ofFinite κ
  refine ⟨Module.Free.of_equiv e, ?_⟩
  have hcard : k + Fintype.card κ = Fintype.card m := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      Fintype.card_congr (rowPartitionEquiv r hr)
  have he : Fintype.card κ = Module.finrank R M := by
    have he₀ : Module.finrank R (κ → R) = Module.finrank R M := e.finrank_eq
    rwa [Module.finrank_fintype_fun_eq_card] at he₀
  omega

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
