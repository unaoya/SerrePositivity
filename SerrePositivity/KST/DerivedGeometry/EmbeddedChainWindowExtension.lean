module

public import SerrePositivity.KST.DerivedGeometry.EmbeddedChainWindow

/-!
概要：存在を証明した小さい窓の延長から、帰納に使う具体的な窓を選ぶ。
方針：選択は証明済みの存在にだけ適用し、元の窓の左項を新しい右項に保持する。
規約：準同型分解や K-injectivity の未証明な存在フィールドを導入しない。
使われ方：Stacks Lemma 19.12.2、TT §3・§8、Toën §3.2 の非輪状部分複体の組み立て。
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
  {A : ChainComplex C ℕ} {Q : C} {k : ℕ} (W : EmbeddedChainWindow A Q k)
  (hA : A.ExactAt (k + 1))

/--
概要：証明済みの存在から選んだ小さい先行項、全射、微分、包含とその法則。
方針：有限の窓の存在定理に選択を適用する。
規約：存在を入力フィールドで要求しない。
使われ方：Stacks 19.12.2、TT §3 の帰納の選択データ。
-/
def chainWindowExtensionData :
    Σ' (X : C) (a : (∐ fun _ : Shrink.{w} (Subobject Q) => G) ⟶ X)
      (d : X ⟶ W.left) (j : X ⟶ A.X (k + 2)), Epi a ∧ Mono j ∧
      d ≫ W.leftι = j ≫ A.d (k + 2) (k + 1) ∧
      ∃ hz : d ≫ W.d = 0, (ShortComplex.mk d W.d hz).Exact := by
  apply Classical.choice
  obtain ⟨X, a, d, j, ha, hj, hc, hz, he⟩ := W.extension_exists G hG hA
  exact ⟨⟨X, a, d, j, ha, hj, hc, hz, he⟩⟩

/--
概要：小さい先行項を加えた次の具体的な窓。
方針：新しい右項には元の左項をそのまま置く。
規約：射の型の同一性が自然数の帰納で保たれる。
使われ方：Stacks 19.12.2、TT §3 の自然数方向の構成。
-/
def EmbeddedChainWindow.extend :
    EmbeddedChainWindow A (∐ fun _ : Shrink.{w} (Subobject Q) => G) (k + 1) where
  left := (chainWindowExtensionData G hG W hA).1
  right := W.left
  d := (chainWindowExtensionData G hG W hA).2.2.1
  leftι := (chainWindowExtensionData G hG W hA).2.2.2.1
  rightι := W.leftι
  left_mono := (chainWindowExtensionData G hG W hA).2.2.2.2.2.1
  right_mono := W.left_mono
  comm := (chainWindowExtensionData G hG W hA).2.2.2.2.2.2.1
  cover := (chainWindowExtensionData G hG W hA).2.1
  cover_epi := (chainWindowExtensionData G hG W hA).2.2.2.2.1

/--
概要：選んだ先行微分と元の微分の合成は零。
方針：構成した窓の延長の法則を取り出す。
規約：元の左項を次の右項として保持した同一の型上の等式。
使われ方：Stacks 19.12.2、TT §3 の鎖複体の二乗零。
-/
lemma EmbeddedChainWindow.extend_zero : (W.extend G hG hA).d ≫ W.d = 0 :=
  (chainWindowExtensionData G hG W hA).2.2.2.2.2.2.2.choose

/--
概要：新しい微分と元の微分の短複体は完全。
方針：小さい先行項の存在で証明した完全性を使う。
規約：各窓の中央での完全性。
使われ方：Stacks 19.12.2、TT §3 の非輪状性の帰納。
-/
lemma EmbeddedChainWindow.extend_exact :
    (ShortComplex.mk (W.extend G hG hA).d W.d (W.extend_zero G hG hA)).Exact :=
  (chainWindowExtensionData G hG W hA).2.2.2.2.2.2.2.choose_spec

end SerrePositivity.KST.DerivedGeometry
