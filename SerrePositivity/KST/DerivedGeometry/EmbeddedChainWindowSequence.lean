module

public import SerrePositivity.KST.DerivedGeometry.EmbeddedChainWindowExtension

/-!
概要：小さい商の窓を自然数方向へ順に完全に延長する列。
方針：各段階の上界を固定対象の部分対象集合で添字付けた生成対象の直和として定める。
規約：列と上界は同時に実際の帰納定義で与える。
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

/--
概要：小さい先行項の呈示に使う固定対象の列。
方針：前段階の部分対象集合上で生成対象の直和を取る。
規約：部分複体の具体的な射の選択に依存しない。
使われ方：Stacks 19.12.2、TT §3 の試験族の統一した上界。
-/
def smallChainWindowBounds (G Q : C) : ℕ → C
  | 0 => Q
  | n + 1 => ∐ fun _ : Shrink.{w} (Subobject (smallChainWindowBounds G Q n)) => G

/--
概要：初期の窓を小さい先行項で順に延長した具体的な列。
方針：各次数の完全性へ証明済みの窓の延長を適用する。
規約：前段階の左項を次段階の右項として保持する。
使われ方：Stacks 19.12.2、TT §3 の非輪状部分複体の帰納構成。
-/
def embeddedChainWindowSequence (G : C) (hG : IsSeparator G)
    {A : ChainComplex C ℕ} {Q : C} (W : EmbeddedChainWindow A Q 0)
    (hA : ∀ n : ℕ, A.ExactAt (n + 1)) :
    ∀ n : ℕ, EmbeddedChainWindow A (smallChainWindowBounds G Q n) n
  | 0 => W
  | n + 1 => (embeddedChainWindowSequence G hG W hA n).extend G hG (hA n)

end SerrePositivity.KST.DerivedGeometry
