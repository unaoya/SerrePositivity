module

public import SerrePositivity.AlgebraicGeometry.NoetherianFlatFactorization
public import SerrePositivity.AlgebraicGeometry.FiniteTypeCountableGeneration

/-!
概要：KST §5、Stacks 05DP・059X・058E の Noether 基底上の平坦加群の有限自由近似列。
方針：核を保ち指定元を追加する一段の構成を、零加群から再帰的に選ぶ。
規約：各評価写像と遷移写像を実際に構成し、極限・射影性の存在をデータに含めない。
使われ方：可算生成平坦加群の射影性判定への有限自由段階の入力。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：加群への評価を持つ一つの有限自由近似段階。
方針：自然数の階数と実際の有限台関数加群からの評価写像を保持する。
規約：KST §5、Stacks 05DP・059X、評価写像の全射性は要求しない。
使われ方：逐次的な有限自由近似の状態。
-/
structure FiniteFreeStage (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M] where
  rank : ℕ
  eval : (Fin rank →₀ R) →ₗ[R] M

/--
概要：元の評価の核を消し、指定元を評価像に追加する一段の有限自由細分。
方針：次の段階、遷移、指定元の持ち上げと、それらの実際の等式を保持する。
規約：KST §5、Stacks 05DP・059X、存在そのものは後続の構成で証明する。
使われ方：有限自由近似列の各後続段階。
-/
structure FiniteFreeRefinement {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (X : FiniteFreeStage R M) (m : M) where
  next : FiniteFreeStage R M
  transition : (Fin X.rank →₀ R) →ₗ[R] (Fin next.rank →₀ R)
  lift : Fin next.rank →₀ R
  eval_comp : next.eval.comp transition = X.eval
  ker_eq : LinearMap.ker transition = LinearMap.ker X.eval
  eval_lift : next.eval lift = m

/--
概要：Noether 基底上の平坦加群の任意の有限自由近似と指定元に実際の一段細分を選べる。
方針：核を保ち指定元を追加する因子化の既証の存在からデータを選ぶ。
規約：KST §5、Stacks 05DP・059X・058E、有限自由細分の存在を仮定せず構成する。
使われ方：逐次近似の後続を定める。
-/
def flatFiniteFreeRefinement {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (X : FiniteFreeStage R M) (m : M) :
    FiniteFreeRefinement X m := by
  apply Classical.choice
  obtain ⟨k, a, b, v, hba, hker, hv⟩ :=
    exists_finiteFree_factorization_same_kernel_and_element X.eval m
  exact ⟨⟨⟨k, b⟩, a, v, hba, hker, hv⟩⟩

/--
概要：指定元の列を一つずつ評価像に含める平坦加群の実際の有限自由近似列。
方針：零の初段から、核を保つ細分の次段を再帰的に取る。
規約：KST §5、Stacks 05DP・059X、基礎環は Noether、指定列の生成性は定義には不要。
使われ方：可算生成加群の有限自由近似。
-/
def flatFiniteFreeStage {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (g : ℕ → M) : ℕ → FiniteFreeStage R M
  | 0 => ⟨0, 0⟩
  | n + 1 => (flatFiniteFreeRefinement (flatFiniteFreeStage (R := R) g n) (g n)).next

/--
概要：逐次的な有限自由近似の実際の遷移線形写像。
方針：選んだ一段細分の遷移成分を取る。
規約：KST §5、Stacks 05DP・059X、始域と終域の階数は近似列から取る。
使われ方：評価写像の可換式と核の正確な消去。
-/
def flatFiniteFreeTransition {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (g : ℕ → M) (n : ℕ) :
    (Fin (flatFiniteFreeStage (R := R) g n).rank →₀ R) →ₗ[R]
      (Fin (flatFiniteFreeStage (R := R) g (n + 1)).rank →₀ R) :=
  (flatFiniteFreeRefinement (flatFiniteFreeStage (R := R) g n) (g n)).transition

/--
概要：有限自由近似の遷移は評価写像と可換。
方針：各一段細分の合成式を使う。
規約：KST §5、Stacks 05DP・059X、等式は実際の線形写像の間で述べる。
使われ方：近似列から元の加群への整合的な評価。
-/
theorem flatFiniteFreeTransition_eval {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (g : ℕ → M) (n : ℕ) :
    (flatFiniteFreeStage (R := R) g (n + 1)).eval.comp (flatFiniteFreeTransition (R := R) g n) =
      (flatFiniteFreeStage (R := R) g n).eval :=
  (flatFiniteFreeRefinement (flatFiniteFreeStage (R := R) g n) (g n)).eval_comp

/--
概要：元の加群への評価の核は、次段への遷移の核に正確に一致する。
方針：各一段細分の核の等式を使う。
規約：KST §5、Stacks 05DP・059X、関係式は直後の段階で全て消える。
使われ方：有限自由近似列の極限を元の加群と比較する。
-/
theorem flatFiniteFreeTransition_ker {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (g : ℕ → M) (n : ℕ) :
    LinearMap.ker (flatFiniteFreeTransition (R := R) g n) =
      LinearMap.ker (flatFiniteFreeStage (R := R) g n).eval :=
  (flatFiniteFreeRefinement (flatFiniteFreeStage (R := R) g n) (g n)).ker_eq

/--
概要：列の n 番目の指定元は n+1 番目の有限自由近似の評価像に含まれる。
方針：一段細分に構成した持ち上げを使う。
規約：KST §5、Stacks 05DP・059X、指定列の生成性は不要。
使われ方：指定列が生成するとき評価像が全体を覆うことを示す。
-/
theorem mem_range_flatFiniteFreeStage_succ {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (g : ℕ → M) (n : ℕ) :
    g n ∈ LinearMap.range (flatFiniteFreeStage (R := R) g (n + 1)).eval :=
  ⟨(flatFiniteFreeRefinement (flatFiniteFreeStage (R := R) g n) (g n)).lift,
    (flatFiniteFreeRefinement (flatFiniteFreeStage (R := R) g n) (g n)).eval_lift⟩

/--
概要：指定列が加群を生成するとき、有限自由近似の評価像の上限は全体。
方針：各指定元が後続評価像に入ることから線形包の包含を得る。
規約：KST §5、Stacks 05DP・059X、極限の普遍性は別途扱う。
使われ方：可算生成平坦加群を近似列全体で覆う。
-/
theorem iSup_range_flatFiniteFreeStage {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Flat R M] (g : ℕ → M)
    (hg : Submodule.span R (Set.range g) = ⊤) :
    (⨆ n, LinearMap.range (flatFiniteFreeStage (R := R) g n).eval) = ⊤ := by
  apply top_unique
  rw [← hg]
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact (le_iSup (fun k => LinearMap.range (flatFiniteFreeStage (R := R) g k).eval) (n + 1))
    (mem_range_flatFiniteFreeStage_succ (R := R) g n)

/--
概要：Noether 基底上可算生成で平坦な加群には、評価像が全体を覆い核を直後に消す有限自由近似列が存在する。
方針：実際の自然数生成元列を選び、指定元を逐次追加する構成の可換式と核の等式を合わせる。
規約：KST §5、Stacks 05DP・059X、射影性と極限の普遍性はこの結論に含めない。
使われ方：Mittag–Leffler 性の有限自由段階による判定の入力。
-/
theorem exists_flatFiniteFree_sequence
    {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (hM : HasCountableGeneratingSet R M) :
    ∃ (X : ℕ → FiniteFreeStage R M)
      (a : ∀ n, (Fin (X n).rank →₀ R) →ₗ[R] (Fin (X (n + 1)).rank →₀ R)),
      (∀ n, (X (n + 1)).eval.comp (a n) = (X n).eval) ∧
      (∀ n, LinearMap.ker (a n) = LinearMap.ker (X n).eval) ∧
      (⨆ n, LinearMap.range (X n).eval) = ⊤ := by
  obtain ⟨g, hg⟩ := hM.exists_nat_spanning
  exact ⟨flatFiniteFreeStage (R := R) g, flatFiniteFreeTransition (R := R) g,
    flatFiniteFreeTransition_eval g, flatFiniteFreeTransition_ker g,
    iSup_range_flatFiniteFreeStage g hg⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
