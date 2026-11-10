module

public import SerrePositivity.AlgebraicGeometry.BlowupAway
public import SerrePositivity.AlgebraicGeometry.FiberFreeOpenUniversalInjectivity
public import SerrePositivity.AlgebraicGeometry.PureTransformFlatExtension
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


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
-- 帰納仮定に有限加群の商の二つのスカラー作用を渡す。
/--
概要：全ファイバーと交わる自由化主開がある場合、台の次元の小さい加群を平坦化する帰納仮定を適用できる。
方針：一つの普遍単射の余核を取り、境界外での平坦性と次元降下を帰納仮定に渡す。
規約：許容開は基底の一つの主開とし、帰納仮定は同じ有限型代数上で述べる。
使われ方：Stacks 0815 の滑らかで幾何学的整な正規化先における帰納段階。
-/
theorem exists_affine_flatPure_center_of_smaller_fiber_cokernels
    {R : CommRingCat.{u}} {B N : Type u} [CommRing B] [Algebra R B] [Module.Projective R B]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] [Module.Finite B N]
    (a : R) [Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] N)]
    (b : B) [Nontrivial (Localization.Away b)]
    [Module.Free (Localization.Away b) (Localization.Away b ⊗[B] N)]
    (hDom : ∀ p : PrimeSpectrum R, IsDomain (B ⊗[R] p.asIdeal.ResidueField))
    (hb : ∀ p : PrimeSpectrum R, algebraMap B (B ⊗[R] p.asIdeal.ResidueField) b ≠ 0)
    (d : WithBot ℕ∞) (hd : ∀ p : PrimeSpectrum R, ringKrullDim (B ⊗[R] p.asIdeal.ResidueField) ≤ d)
    (hrec : ∀ (P : Type u) [AddCommGroup P] [Module R P] [Module B P]
      [IsScalarTower R B P] [Module.Finite B P],
      (∀ p : PrimeSpectrum R, let C := B ⊗[R] p.asIdeal.ResidueField
        Module.supportDim C (C ⊗[B] P) + 1 ≤ d) →
      Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] P) →
      ∃ I : Ideal R, I.FG ∧ PrimeSpectrum.basicOpen a ≤ affineCenterComplement I ∧
        HasFlatPurePullbacks (affineBlowupπ I) a P) :
    ∃ I : Ideal R, I.FG ∧ PrimeSpectrum.basicOpen a ≤ affineCenterComplement I ∧
      HasFlatPurePullbacks (affineBlowupπ I) a N := by
  classical
  obtain ⟨ι, _, f, hf, hdim⟩ := exists_universal_free_map_with_smaller_fiber_support (N := N) b hDom hb
  let : Module.Projective R (ι →₀ B) :=
    Module.Projective.of_equiv' (finsuppLequivDFinsupp (ι := ι) (M := B) R).symm
  let P := N ⧸ LinearMap.range f
  let g : N →ₗ[R] P := (LinearMap.range f).mkQ.restrictScalars R
  have hex : Function.Exact (f.restrictScalars R) g := f.exact_map_mkQ_range
  have hg : Function.Surjective g := Submodule.mkQ_surjective _
  have hflat : Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] P) :=
    flat_right_baseChange_of_lTensor_injective (f.restrictScalars R) g hex hg hf
  have hPdim (p : PrimeSpectrum R) :
      let C := B ⊗[R] p.asIdeal.ResidueField
      Module.supportDim C (C ⊗[B] P) + 1 ≤ d := (hdim p).trans (hd p)
  obtain ⟨I, hI, ha, hP⟩ := hrec P hPdim hflat
  exact ⟨I, hI, ha, hP.of_flat_source_exact (f.restrictScalars R) g hex hg hf⟩

end SerrePositivity.AlgebraicGeometry
