module

public import SerrePositivity.KST.DerivedGeometry.SmallExactChainProperties
public import SerrePositivity.KST.DerivedGeometry.InitialImageChainWindow

/-!
概要：生成対象からの射の像を含む、小さい非輪状な自然数鎖複体を構成する。
方針：初期像窓の全射性と全正次数の完全な窓の延長を組み合わせる。
規約：各項の上界は生成対象だけから定める。
使われ方：Stacks Lemma 19.12.2、TT §3・§8、Toën §3.2 の上に有界な非輪状部分複体。
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
概要：初期微分が全射なら小さい窓の鎖複体は非輪状。
方針：零次数は初期微分の全射性、正次数は窓の完全性を使う。
規約：全自然数次数の完全性。
使われ方：Stacks 19.12.2、TT §3 の小さい非輪状複体。
-/
lemma smallExactChainTail_acyclic [Epi W.d] : (smallExactChainTail G hG W hA).Acyclic := by
  intro n
  cases n with
  | zero =>
    rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)]
    change (ShortComplex.mk ((smallExactChainTail G hG W hA).d 1 0)
      ((smallExactChainTail G hG W hA).d 0 0) _).Exact
    apply (ShortComplex.exact_iff_epi _
      ((smallExactChainTail G hG W hA).shape 0 0 (by decide))).mpr
    change Epi ((smallExactChainTail G hG W hA).d 1 0)
    rw [smallExactChainTail_d]
    exact inferInstanceAs (Epi W.d)
  | succ n => exact smallExactChainTail_exactAt_succ G hG W hA n

/--
概要：小さい部分複体の全ての次数の項を商として含む固定対象。
方針：帰納的に定めた呈示対象の列の直和を取る。
規約：対象は生成対象だけに依存し、複体や指定した射には依存しない。
使われ方：Stacks 19.12.2、TT §3 の小さい試験集合の統一した上界。
-/
def smallAcyclicUniformBound (G : C) : C := ∐ (smallChainWindowBounds G G)

/--
概要：統一した上界の対象から各段階の呈示対象への全射。
方針：直和の各項への標準射は対応する包含を右逆に持つ。
規約：自然数添字の直和。
使われ方：Stacks 19.12.2、TT §3 の全ての項の商呈示。
-/
instance smallAcyclicUniformBound_projection_epi (G : C) (n : ℕ) :
    Epi (Sigma.π (smallChainWindowBounds G G) n) := inferInstance

end SerrePositivity.KST.DerivedGeometry
