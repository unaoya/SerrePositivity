module

public import SerrePositivity.AlgebraicGeometry.LinearLiftMittagLeffler
public import SerrePositivity.AlgebraicGeometry.FlatFiniteFreeDirectLimit

/-!
概要：KST §5、Stacks 059X, Lemma 10.93.1 の Noether 基底上の可算生成平坦 Mittag–Leffler 加群の射影性。
方針：有限自由近似の整合的持ち上げを直極限へ移し、自由全射の実際の右逆を構成する。
規約：Noether 性は有限自由近似列の構成で使い、射影性を仮定しない。
使われ方：05DP・05FS の完備化による Mittag–Leffler 性から実分裂へ戻る。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.AlgebraicGeometry

/--
概要：Mittag–Leffler 加群を表す有限自由列の評価先への任意の全射は、実際の線形右逆を持つ。
方針：全段階の整合的な持ち上げを直極限へ移し、評価同型の逆で元の加群へ戻す。
規約：KST §5、Stacks 059X, Lemma 10.93.1、列の核消去と像の被覆を明示する。
使われ方：自由全射を分裂して元の加群の射影性を証明する。
-/
theorem exists_linearSection_of_finiteFree_sequence_mittagLeffler
    (R : Type u) [CommRing R] (F : ℕ → Type u)
    [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]
    {σ : ℕ → Type v} [∀ n, Finite (σ n)] (b : ∀ n, Module.Basis (σ n) R (F n))
    (a : ∀ n, F n →ₗ[R] F (n + 1))
    {M E : Type u} [AddCommGroup M] [Module R M] [AddCommGroup E] [Module R E]
    (q : ∀ n, F n →ₗ[R] M) (hq : ∀ n, (q (n + 1)).comp (a n) = q n)
    (hker : ∀ n, LinearMap.ker (a n) = LinearMap.ker (q n))
    (hcover : (⨆ n, LinearMap.range (q n)) = ⊤) (hM : IsModuleMittagLeffler R M)
    (π : E →ₗ[R] M) (hπ : Function.Surjective π) :
    ∃ s : M →ₗ[R] E, π.comp s = LinearMap.id := by
  obtain ⟨l, hπl, hl⟩ := exists_compatible_linearSequence_lifts_of_mittagLeffler
    R F b a q hq π hπ hker hcover hM
  let E₀ := linearSequenceDirectLimitEquiv R F a q hq hker hcover
  let L := linearSequenceLimitEval R F a l hl
  refine ⟨L.comp E₀.symm.toLinearMap, ?_⟩
  ext m
  obtain ⟨z, rfl⟩ := E₀.surjective m
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk (linearSequenceMap R F a) z
  change π (L (E₀.symm (E₀ (DirectLimit.Module.of R ℕ F (linearSequenceMap R F a) n x)))) =
    E₀ (DirectLimit.Module.of R ℕ F (linearSequenceMap R F a) n x)
  rw [E₀.symm_apply_apply]
  change π (l n x) = q n x
  exact congrArg (fun f : F n →ₗ[R] M => f x) (hπl n)

/--
概要：核を直後に消し像が全体を覆う有限自由列で表される Mittag–Leffler 加群は射影的。
方針：元の加群を添字とする自由全射へ右逆を作り、自由加群の直和因子として射影性を得る。
規約：KST §5、Stacks 059X, Lemma 10.93.1、Noether 性と平坦性は列の構成後には不要。
使われ方：可算生成平坦加群の構成済みの近似列へ適用する。
-/
theorem projective_of_finiteFree_sequence_mittagLeffler
    (R : Type u) [CommRing R] (F : ℕ → Type u)
    [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]
    {σ : ℕ → Type v} [∀ n, Finite (σ n)] (b : ∀ n, Module.Basis (σ n) R (F n))
    (a : ∀ n, F n →ₗ[R] F (n + 1))
    {M : Type u} [AddCommGroup M] [Module R M]
    (q : ∀ n, F n →ₗ[R] M) (hq : ∀ n, (q (n + 1)).comp (a n) = q n)
    (hker : ∀ n, LinearMap.ker (a n) = LinearMap.ker (q n))
    (hcover : (⨆ n, LinearMap.range (q n)) = ⊤) (hM : IsModuleMittagLeffler R M) :
    Module.Projective R M := by
  let π : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  obtain ⟨s, hs⟩ := exists_linearSection_of_finiteFree_sequence_mittagLeffler
    R F b a q hq hker hcover hM π (Finsupp.linearCombination_id_surjective R M)
  exact Module.Projective.of_split s π hs

/--
概要：Noether 基礎環上の可算生成平坦 Mittag–Leffler 加群は射影的。
方針：実際の自然数生成元列と有限自由近似を構成し、自由全射の右逆による射影性判定へ渡す。
規約：KST §5、Stacks 059X, Lemma 10.93.1 の Noether 特殊形、追加公理と射影性の仮定なし。
使われ方：完備化から降下させた Mittag–Leffler 性を実分裂に変える。
-/
theorem projective_of_countable_flat_mittagLeffler
    {R M : Type u} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (hcount : HasCountableGeneratingSet R M) (hM : IsModuleMittagLeffler R M) :
    Module.Projective R M := by
  obtain ⟨g, hg⟩ := hcount.exists_nat_spanning
  let F (n : ℕ) := Fin (flatFiniteFreeStage (R := R) g n).rank →₀ R
  let b (n : ℕ) : Module.Basis (Fin (flatFiniteFreeStage (R := R) g n).rank) R (F n) :=
    Finsupp.basisSingleOne
  exact projective_of_finiteFree_sequence_mittagLeffler R F b
    (flatFiniteFreeTransition (R := R) g)
    (fun n => (flatFiniteFreeStage (R := R) g n).eval)
    (flatFiniteFreeTransition_eval g) (flatFiniteFreeTransition_ker g)
    (iSup_range_flatFiniteFreeStage g hg) hM

/--
概要：Noether 基礎環の有限型代数上有限で、基礎環上平坦かつ Mittag–Leffler な加群は射影的。
方針：単項式と有限生成元による可算生成性を、証明済みの可算生成平坦 Mittag–Leffler 判定へ渡す。
規約：KST §5、Stacks 05DP・059X、完備化に関する仮定は Mittag–Leffler 性の別の証明に属する。
使われ方：05DP の完備化経路の最後に有限型加群の射影性を得る。
-/
theorem projective_of_finiteType_finite_flat_mittagLeffler
    (R B M : Type u) [CommRing R] [IsNoetherianRing R] [CommRing B] [Algebra R B]
    [Algebra.FiniteType R B] [AddCommGroup M] [Module R M] [Module B M]
    [IsScalarTower R B M] [Module.Finite B M] [Module.Flat R M]
    (hM : IsModuleMittagLeffler R M) : Module.Projective R M :=
  projective_of_countable_flat_mittagLeffler
    (hasCountableGeneratingSet_of_finiteType_finite R B M) hM

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
