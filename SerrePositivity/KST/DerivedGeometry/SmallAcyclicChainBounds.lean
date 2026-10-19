module

public import SerrePositivity.KST.DerivedGeometry.SmallAcyclicChainTail

/-!
概要：生成対象だけから定まる一つの対象で、小さい非輪状鎖複体の全項を商として呈示する。
方針：帰納上界の直和の射影と、各窓の標準全射を合成する。
規約：複体も指定した射も上界の対象を変更しない。
使われ方：Stacks Lemma 19.12.2、TT §3・§8、Toën §3.2 の小さい試験集合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (hG : IsSeparator G) (A : ChainComplex C ℕ) (ψ : G ⟶ A.X 1)
  (hA : ∀ n : ℕ, A.ExactAt (n + 1))

/--
概要：統一した上界から、指定した射の像を含む小さい鎖複体の各項への全射。
方針：零次数には微分の像への全射、正次数には窓の呈示を用いる。
規約：上界は生成対象だけの関数。
使われ方：Stacks 19.12.2、TT §3 の商の小さい代表族への接続。
-/
def smallAcyclicChainCover : ∀ n : ℕ, smallAcyclicUniformBound G ⟶
    (smallExactChainTail G hG (initialImageChainWindow A ψ) hA).X n
  | 0 => Sigma.π (smallChainWindowBounds G G) 0 ≫ factorThruImage (ψ ≫ A.d 1 0)
  | n + 1 => Sigma.π (smallChainWindowBounds G G) n ≫
      (embeddedChainWindowSequence G hG (initialImageChainWindow A ψ) hA n).cover

/--
概要：統一した上界から各項への標準射は全射。
方針：直和の射影と、像分解または窓の全射の合成を使う。
規約：全自然数次数。
使われ方：Stacks 19.12.2、TT §3 の小さい試験族の各項の上界。
-/
instance smallAcyclicChainCover_epi (n : ℕ) : Epi (smallAcyclicChainCover G hG A ψ hA n) := by
  cases n with
  | zero => change Epi (Sigma.π (smallChainWindowBounds G G) 0 ≫ factorThruImage (ψ ≫ A.d 1 0))
            infer_instance
  | succ n =>
    change Epi (Sigma.π (smallChainWindowBounds G G) n ≫
      (embeddedChainWindowSequence G hG (initialImageChainWindow A ψ) hA n).cover)
    infer_instance

end SerrePositivity.KST.DerivedGeometry
