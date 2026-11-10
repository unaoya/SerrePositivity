module

public import SerrePositivity.AlgebraicGeometry.FiberFreeOpenUniversalInjectivity
public import Mathlib.Data.Finsupp.ToDFinsupp

/-!
概要：自由化主開を一つ選ぶと、普遍単射な有限自由部分とファイバー次元の小さい余核が得られる。
方針：同じ自由化写像について各ファイバーでの次元降下と普遍単射性を合わせる。
規約：正規化先の代数は基底上射影とし、ファイバーは整とする。
使われ方：Stacks 0815 の台の次元による帰納で余核を選ぶ。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

/--
概要：全整ファイバーと交わる一つの主開で自由なら、普遍単射な有限自由部分の余核は全ファイバーで台の次元が下がる。
方針：主開での基底の分母を払い、一つの写像で普遍単射性と生成点での同型を得る。
規約：ファイバー次元の比較は正規化先のファイバー環の Krull 次元に対して行う。
使われ方：次元を抑えた滑らかな正規化先上で余核に帰納を適用する。
-/
theorem exists_universal_free_map_with_smaller_fiber_support
    {R B N : Type u} [CommRing R] [CommRing B] [Algebra R B] [Module.Projective R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] [Module.Finite B N]
    (b : B) [Nontrivial (Localization.Away b)]
    [Module.Free (Localization.Away b) (Localization.Away b ⊗[B] N)]
    (hDom : ∀ p : PrimeSpectrum R, IsDomain (B ⊗[R] p.asIdeal.ResidueField))
    (hb : ∀ p : PrimeSpectrum R, algebraMap B (B ⊗[R] p.asIdeal.ResidueField) b ≠ 0) :
    ∃ (ι : Type u) (_ : Finite ι) (f : (ι →₀ B) →ₗ[B] N),
      (∀ (Q : Type u) [AddCommGroup Q] [Module R Q],
        Function.Injective ((f.restrictScalars R).lTensor Q)) ∧
      ∀ p : PrimeSpectrum R, let A := B ⊗[R] p.asIdeal.ResidueField
        Module.supportDim A (A ⊗[B] (N ⧸ LinearMap.range f)) + 1 ≤ ringKrullDim A := by
  classical
  obtain ⟨ι, hι, f, hf⟩ := exists_finite_free_map_bijective_away (N := N) b
  let : Module.Projective R (ι →₀ B) :=
    Module.Projective.of_equiv' (finsuppLequivDFinsupp (ι := ι) (M := B) R).symm
  refine ⟨ι, hι, f, fun Q _ _ => lTensor_injective_of_away_bijective_in_fibers f b hDom hb hf Q,
    fun p => ?_⟩
  let : IsDomain (B ⊗[R] p.asIdeal.ResidueField) := hDom p
  exact supportDim_baseChange_cokernel_add_one_le_of_away_bijective f b (hb p) hf

end SerrePositivity.AlgebraicGeometry
