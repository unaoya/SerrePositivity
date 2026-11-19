module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.LinearLiftInverseFunctor
public import SerrePositivity.AlgebraicGeometry.FiniteLiftCorrection
public import SerrePositivity.AlgebraicGeometry.NatInverseSections
public import SerrePositivity.AlgebraicGeometry.MittagLefflerDualStabilization

/-!
概要：KST §5、Stacks 05DP・059X の有限自由列から全射への持ち上げの整合的選択。
方針：双対像の安定化と核値補正で持ち上げ逆系を Mittag–Leffler とし、非空 section を取る。
規約：各段階の自由性による持ち上げは実際に構成し、整合性を仮定しない。
使われ方：元の加群への全射の線形右逆を直極限から作る。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.FunctorToTypes

variable (R : Type u) [CommRing R] (F : ℕ → Type u)
  [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]
  {σ : ℕ → Type v} [∀ n, Finite (σ n)] (b : ∀ n, Module.Basis (σ n) R (F n))
  (a : ∀ n, F n →ₗ[R] F (n + 1))
  {M E : Type u} [AddCommGroup M] [Module R M] [AddCommGroup E] [Module R E]
  (q : ∀ n, F n →ₗ[R] M) (hq : ∀ n, (q (n + 1)).comp (a n) = q n)
  (π : E →ₗ[R] M) (hπ : Function.Surjective π)

include b hπ in
/--
概要：双対遷移像が安定する有限自由列から全射への持ち上げの逆系は Mittag–Leffler。
方針：後段の任意の持ち上げを、核値の差の因子化によって初段で指定の持ち上げに一致させる。
規約：KST §5、Stacks 05DP・059X、各段階の像の安定化を実際の包含で示す。
使われ方：非空な持ち上げ逆系へ自然数 Mittag–Leffler 系の section の存在を適用する。
-/
theorem linearSequenceLiftFunctor_isMittagLeffler_of_stable_dual_ranges
    (hstable : ∀ n : ℕ, ∃ (k : ℕ) (hk : n ≤ k), ∀ (ℓ : ℕ) (hkℓ : k ≤ ℓ),
      LinearMap.range (linearSequenceMap R F a n ℓ (hk.trans hkℓ)).dualMap =
        LinearMap.range (linearSequenceMap R F a n k hk).dualMap) :
    (linearSequenceLiftFunctor R F a q hq π).IsMittagLeffler := by
  classical
  let T := linearSequenceLiftFunctor R F a q hq π
  apply (T.isMittagLeffler_iff_subset_range_comp).mpr
  intro j
  obtain ⟨k, hk, hst⟩ := hstable j.unop
  refine ⟨Opposite.op k, (homOfLE hk).op, ?_⟩
  intro i g
  rintro _ ⟨Φ, rfl⟩
  let ℓ := i.unop
  have hkℓ : k ≤ ℓ := leOfHom g.unop
  let f := linearSequenceMap R F a j.unop k hk
  let f' := linearSequenceMap R F a j.unop ℓ (hk.trans hkℓ)
  let t := linearSequenceMap R F a k ℓ hkℓ
  have ht : t.comp f = f' := by
    ext x
    exact DirectedSystem.map_map' (linearSequenceMap R F a) hk hkℓ x
  let : Module.Projective R (F ℓ) := Module.Projective.of_basis (b ℓ)
  obtain ⟨Ψ, hΨ⟩ := Module.projective_lifting_property π (q ℓ) hπ
  have hcomp : π.comp Φ.val = (π.comp Ψ).comp t := by
    rw [Φ.property, hΨ]
    ext x
    exact (linearSequenceMap_eval R F a q hq k ℓ hkℓ x).symm
  obtain ⟨Ψ', hπ', hcomm⟩ := exists_compatible_lift_of_dual_range_le
    (b k) f f' t ht (hst ℓ hkℓ).ge π Φ.val Ψ hcomp
  refine ⟨⟨Ψ', hπ'.trans hΨ⟩, ?_⟩
  apply Subtype.ext
  exact hcomm

include b hq hπ in
/--
概要：Mittag–Leffler 加群を表す有限自由列は、任意の全射へ全段階で整合的に持ち上げられる。
方針：双対像を安定化し、非空な持ち上げ逆系の section を選ぶ。
規約：KST §5、Stacks 05DP・059X、各段階での持ち上げと後続遷移での可換式を実際に返す。
使われ方：直極限上の持ち上げから全射の右逆を構成する。
-/
theorem exists_compatible_linearSequence_lifts_of_mittagLeffler
    (hker : ∀ n, LinearMap.ker (a n) = LinearMap.ker (q n))
    (hcover : (⨆ n, LinearMap.range (q n)) = ⊤) (hM : IsModuleMittagLeffler R M) :
    ∃ l : ∀ n, F n →ₗ[R] E,
      (∀ n, π.comp (l n) = q n) ∧ (∀ n, (l (n + 1)).comp (a n) = l n) := by
  let T := linearSequenceLiftFunctor R F a q hq π
  let (i : ℕᵒᵖ) : Nonempty (T.obj i) :=
    linearSequenceLiftFunctor_nonempty_of_basis R F a q hq π b hπ i
  have hT : T.IsMittagLeffler :=
    linearSequenceLiftFunctor_isMittagLeffler_of_stable_dual_ranges R F b a q hq π hπ
      (exists_stable_dual_ranges_of_mittagLeffler F b a q hq hker hcover hM)
  obtain ⟨s, hs⟩ := nonempty_sections_of_mittagLeffler_nat_inverse_system T hT
  refine ⟨fun n => (s (Opposite.op n)).val, fun n => (s (Opposite.op n)).property, ?_⟩
  intro n
  have h := congrArg Subtype.val (hs (homOfLE (Nat.le_succ n)).op)
  change (s (Opposite.op (n + 1))).val.comp
      (linearSequenceMap R F a n (n + 1) (Nat.le_succ n)) = (s (Opposite.op n)).val at h
  rwa [linearSequenceMap_succ] at h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
