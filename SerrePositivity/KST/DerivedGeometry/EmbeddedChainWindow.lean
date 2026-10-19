module

public import SerrePositivity.KST.DerivedGeometry.SmallExactWindowExtension
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
概要：小さい商で呈示した隣接二項の埋め込みを持つ鎖複体の窓と、その実際の延長。
方針：完全な短い窓の延長定理から存在を証明し、選択した具体的なデータを帰納に用いる。
規約：有限の窓の項・射・法則を記録する。非有界分解の存在をフィールドには置かない。
使われ方：Stacks Lemma 19.12.2 (079K)、TT §3・§8、Toën §3.2 の小さい部分複体の帰納。
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
概要：鎖複体内の隣接二項の部分窓と左項の商呈示。
方針：二つの項の単射と可換な微分を記録する。
規約：記録するのは具体的な射とその法則だけ。
使われ方：Stacks 19.12.2、TT §3 の自然数方向の帰納。
-/
structure EmbeddedChainWindow (A : ChainComplex C ℕ) (Q : C) (k : ℕ) where
  left : C
  right : C
  d : left ⟶ right
  leftι : left ⟶ A.X (k + 1)
  rightι : right ⟶ A.X k
  left_mono : Mono leftι
  right_mono : Mono rightι
  comm : d ≫ rightι = leftι ≫ A.d (k + 1) k
  cover : Q ⟶ left
  cover_epi : Epi cover

attribute [instance] EmbeddedChainWindow.left_mono EmbeddedChainWindow.right_mono
  EmbeddedChainWindow.cover_epi

/--
概要：鎖複体の窓を一つ左へ完全に延長する具体的データが存在する。
方針：全体の中央での完全性に、構成済みの小さい先行項の存在定理を適用する。
規約：延長先の各項と射を結論として構成する。
使われ方：Stacks 19.12.2、TT §3 の上に有界な非輪状部分複体。
-/
lemma EmbeddedChainWindow.extension_exists (G : C) (hG : IsSeparator G)
    {A : ChainComplex C ℕ} {Q : C} {k : ℕ} (W : EmbeddedChainWindow A Q k)
    (hA : A.ExactAt (k + 1)) :
    ∃ (X : C) (a : (∐ fun _ : Shrink.{w} (Subobject Q) => G) ⟶ X)
      (d : X ⟶ W.left) (j : X ⟶ A.X (k + 2)), Epi a ∧ Mono j ∧
      d ≫ W.leftι = j ≫ A.d (k + 2) (k + 1) ∧
      ∃ hz : d ≫ W.d = 0, (ShortComplex.mk d W.d hz).Exact := by
  have hB : (A.sc' (k + 2) (k + 1) k).Exact :=
    (HomologicalComplex.exactAt_iff' A (k + 2) (k + 1) k (by simp) (by simp)).mp hA
  exact exists_small_exact_window_extension G hG (A.sc' (k + 2) (k + 1) k) hB
    W.d W.leftι W.rightι W.comm W.cover

end SerrePositivity.KST.DerivedGeometry
