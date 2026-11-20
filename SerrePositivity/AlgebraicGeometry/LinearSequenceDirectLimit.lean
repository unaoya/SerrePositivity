module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Colimit.DirectLimit

/-!
概要：KST §5、Stacks 05DP・059X の加群列の直極限と整合的評価の比較。
方針：後続遷移を関手へ延長し、評価の核が次段で消える条件と像の被覆で直極限評価を同型にする。
規約：各遷移・評価は実際の線形写像、直極限は Mathlib の代数的な実装を使う。
使われ方：可算生成平坦加群の構成済みの有限自由近似列を元の加群と同定する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory

variable (R : Type u) [CommRing R] (F : ℕ → Type u)
  [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]
  (a : ∀ n, F n →ₗ[R] F (n + 1))

/--
概要：後続段階の線形写像を自然数の順序圏上の加群関手へ延長する。
方針：ModuleCat の実際の射を Functor.ofSequence に渡す。
規約：KST §5、Stacks 05DP・059X、加群の有限性は不要。
使われ方：任意の n≤m の遷移写像を構成する。
-/
def linearSequenceFunctor : ℕ ⥤ ModuleCat R :=
  Functor.ofSequence (fun n => ModuleCat.ofHom (a n))

/--
概要：任意の二段階 n≤m の間の実際の線形遷移写像。
方針：構成した自然数関手の射を線形写像として読む。
規約：KST §5、Stacks 05DP・059X、順序の証明を明示する。
使われ方：代数的直極限の有向系。
-/
def linearSequenceMap (n m : ℕ) (h : n ≤ m) : F n →ₗ[R] F m :=
  ((linearSequenceFunctor R F a).map (homOfLE h)).hom

/--
概要：延長した遷移の直後の成分は元の後続写像に一致する。
方針：Functor.ofSequence の後続射の計算式を使う。
規約：KST §5、Stacks 05DP・059X、証明の選択に依存しない。
使われ方：直極限で核を直後の段階へ送って消す。
-/
theorem linearSequenceMap_succ (n : ℕ) :
    linearSequenceMap R F a n (n + 1) (Nat.le_succ n) = a n := by
  exact congrArg ModuleCat.Hom.hom (Functor.ofSequence_map_homOfLE_succ
    (fun n => ModuleCat.ofHom (a n)) n)

/--
概要：自然数列の延長線形写像は有向系の恒等・合成の法則を満たす。
方針：加群関手の恒等射・合成保存を各元で評価する。
規約：KST §5、Stacks 05DP・059X、元の後続射に追加の法則は不要。
使われ方：Mathlib の代数的直極限の構造を使う。
-/
instance linearSequenceMap_directedSystem :
    DirectedSystem F (fun ⦃n m⦄ h => linearSequenceMap R F a n m h) where
  map_self {i} x := by
    have h := congrArg (fun f : (linearSequenceFunctor R F a).obj i ⟶
      (linearSequenceFunctor R F a).obj i => f.hom x) ((linearSequenceFunctor R F a).map_id i)
    exact h
  map_map {k j i} hij hjk x := by
    have h := (linearSequenceFunctor R F a).map_comp (homOfLE hij) (homOfLE hjk)
    exact congrArg (fun f : (linearSequenceFunctor R F a).obj i ⟶
      (linearSequenceFunctor R F a).obj k => f.hom x) h.symm

variable {M : Type u} [AddCommGroup M] [Module R M]
  (q : ∀ n, F n →ₗ[R] M) (hq : ∀ n, (q (n + 1)).comp (a n) = q n)

/--
概要：後続射に整合する評価を全自然数関手上の自然変換として構成する。
方針：後続射だけの可換式を NatTrans.ofSequence へ渡す。
規約：KST §5、Stacks 05DP・059X、標的は元の加群の定数関手。
使われ方：直極限評価の全遷移に対する整合性。
-/
def linearSequenceEvaluation : linearSequenceFunctor R F a ⟶
    (Functor.const ℕ).obj (ModuleCat.of R M) :=
  NatTrans.ofSequence (fun n => ModuleCat.ofHom (q n)) (fun n => by
    ext x
    change q (n + 1) (linearSequenceMap R F a n (n + 1) (Nat.le_succ n) x) = q n x
    rw [linearSequenceMap_succ]
    exact congrArg (fun f : F n →ₗ[R] M => f x) (hq n))

include hq in
/--
概要：整合的評価は任意の二段階の延長遷移と可換。
方針：構成した自然変換の自然性を元で評価する。
規約：KST §5、Stacks 05DP・059X、後続射の可換式から導く。
使われ方：代数的直極限の評価写像を定める。
-/
theorem linearSequenceMap_eval (n m : ℕ) (h : n ≤ m) (x : F n) :
    q m (linearSequenceMap R F a n m h x) = q n x := by
  exact congrArg (fun f : ModuleCat.of R (F n) ⟶ ModuleCat.of R M => f.hom x)
    ((linearSequenceEvaluation R F a q hq).naturality (homOfLE h))

/--
概要：整合的評価から列の実際の直極限上の評価線形写像を作る。
方針：延長遷移の有向系と全遷移の整合性を直極限の普遍写像へ渡す。
規約：KST §5、Stacks 05DP・059X、評価像の被覆と核条件は定義には不要。
使われ方：有限自由近似列の直極限を元の加群へ送る。
-/
def linearSequenceLimitEval :
    DirectLimit F (linearSequenceMap R F a) →ₗ[R] M :=
  DirectLimit.Module.lift R ℕ F (linearSequenceMap R F a) q
    (linearSequenceMap_eval R F a q hq)

/--
概要：評価の核が直後の遷移で消える加群列の直極限評価は単射。
方針：直極限の代表元の評価が零なら、直後の代表元も零であることを使う。
規約：KST §5、Stacks 05DP・059X、評価像の被覆と加群の有限性は不要。
使われ方：有限自由近似列の直極限と元の加群の単射比較。
-/
theorem linearSequenceLimitEval_injective
    (hker : ∀ n, LinearMap.ker (a n) = LinearMap.ker (q n)) :
    Function.Injective (linearSequenceLimitEval R F a q hq) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk (linearSequenceMap R F a) z
  have hqx : q n x = 0 := hz
  have hax : a n x = 0 := by
    have hmem : x ∈ LinearMap.ker (q n) := hqx
    rw [← hker n] at hmem
    exact hmem
  have hfac := DirectLimit.Module.of_f (R := R) (G := F)
    (f := linearSequenceMap R F a) (i := n) (j := n + 1) (hij := Nat.le_succ n) (x := x)
  change DirectLimit.Module.of R ℕ F (linearSequenceMap R F a) n x = 0
  rw [linearSequenceMap_succ, hax, map_zero] at hfac
  exact hfac.symm

/--
概要：評価像の上限が全体である加群列の直極限評価は全射。
方針：各段階の評価像は直極限評価像に含まれることを使う。
規約：KST §5、Stacks 05DP・059X、核の消去条件は全射性には不要。
使われ方：有限自由近似列の直極限と元の加群の全射比較。
-/
theorem linearSequenceLimitEval_surjective
    (hcover : (⨆ n, LinearMap.range (q n)) = ⊤) :
    Function.Surjective (linearSequenceLimitEval R F a q hq) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hcover]
  apply iSup_le
  intro n
  rintro _ ⟨x, rfl⟩
  exact ⟨DirectLimit.Module.of R ℕ F (linearSequenceMap R F a) n x, rfl⟩

/--
概要：評価像が全体を覆い核が直後に消える加群列の直極限は、評価先の加群と実際に線形同型。
方針：直極限評価の単射性と全射性から線形同型を作る。
規約：KST §5、Stacks 05DP・059X、対象の同一視ではなく評価線形同型を返す。
使われ方：構成済みの有限自由近似列を元の平坦加群と同定する。
-/
def linearSequenceDirectLimitEquiv
    (hker : ∀ n, LinearMap.ker (a n) = LinearMap.ker (q n))
    (hcover : (⨆ n, LinearMap.range (q n)) = ⊤) :
    DirectLimit F (linearSequenceMap R F a) ≃ₗ[R] M :=
  LinearEquiv.ofBijective (linearSequenceLimitEval R F a q hq)
    ⟨linearSequenceLimitEval_injective R F a q hq hker,
      linearSequenceLimitEval_surjective R F a q hq hcover⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
