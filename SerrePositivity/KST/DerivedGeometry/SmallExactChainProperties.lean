module

public import SerrePositivity.KST.DerivedGeometry.SmallExactChainTail

/-!
概要：小さい窓から組み立てた鎖複体の埋め込みと完全性。
方針：隣接する微分を各窓の微分と同定し、各窓での証明を使う。
規約：初期微分が全射なら零次数も完全になる。
使われ方：Stacks Lemma 19.12.2、TT §3・§8、Toën §3.2 の小さい非輪状部分複体。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (hG : IsSeparator G)
  {A : ChainComplex C ℕ} {Q : C} (W : EmbeddedChainWindow A Q 0)
  (hA : ∀ n : ℕ, A.ExactAt (n + 1))

/--
概要：小さい窓の鎖複体の各項の包含。
方針：各窓の既存の単射を用いる。
規約：零次数には初期右項の包含を使う。
使われ方：Stacks 19.12.2、TT §3 の部分複体の包含。
-/
def smallExactChainTermInclusion : ∀ n : ℕ,
    (smallExactChainTail G hG W hA).X n ⟶ A.X n
  | 0 => W.rightι
  | n + 1 => (embeddedChainWindowSequence G hG W hA n).leftι

/--
概要：小さい窓の鎖複体から全体の鎖複体への鎖写像。
方針：各窓の可換性を使う。
規約：全項で既存の包含を保つ。
使われ方：Stacks 19.12.2、TT §3 の部分複体の実際の射。
-/
def smallExactChainInclusion : smallExactChainTail G hG W hA ⟶ A :=
  ChainComplex.ofHom (smallExactChainTermInclusion G hG W hA) (by
    intro n
    rw [smallExactChainTail_d]
    cases n with
    | zero => exact W.comm.symm
    | succ n => exact (embeddedChainWindowSequence G hG W hA (n + 1)).comm.symm)

/--
概要：小さい窓の鎖複体の包含は各項で単射。
方針：具体的な各窓の包含の単射性を使う。
規約：全自然数次数。
使われ方：Stacks 19.12.2、TT §3 の部分複体の単射性。
-/
instance smallExactChainInclusion_f_mono (n : ℕ) : Mono ((smallExactChainInclusion G hG W hA).f n) := by
  cases n with
  | zero => exact W.right_mono
  | succ n => exact (embeddedChainWindowSequence G hG W hA n).left_mono

/--
概要：小さい窓の鎖複体は全正次数で完全。
方針：隣接微分の完全性を構成した窓の延長へ帰着する。
規約：零次数の完全性とは区別する。
使われ方：Stacks 19.12.2、TT §3 の非輪状性の帰納。
-/
lemma smallExactChainTail_exactAt_succ (n : ℕ) :
    (smallExactChainTail G hG W hA).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  change (ShortComplex.mk ((smallExactChainTail G hG W hA).d (n + 2) (n + 1))
    ((smallExactChainTail G hG W hA).d (n + 1) n) _).Exact
  simp only [smallExactChainTail_d]
  cases n with
  | zero => exact W.extend_exact G hG (hA 0)
  | succ n =>
    exact (embeddedChainWindowSequence G hG W hA (n + 1)).extend_exact G hG (hA (n + 1))

end SerrePositivity.KST.DerivedGeometry
