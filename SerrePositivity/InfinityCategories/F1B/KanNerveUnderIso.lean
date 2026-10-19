module

public import SerrePositivity.InfinityCategories.F1B.KanNerveUnderReadChain
public import SerrePositivity.InfinityCategories.F1B.KanNerveUnderChainInverse

/-!
概要：Under c の nerve と c 下の native な coslice を同型にする。
方針：各単体を先頭固定の射列を介して往復させる。
規約：同じ宇宙の小さい圏を扱い、始対象性は仮定しない。
使われ方：B5 の pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {C : Type u} [Category.{u} C] (c : C)

/-- 概要：coslice の単体から Under c の単体を復元する。
方針：読み取った射列と先頭の等式を逆構成へ渡す。
規約：次元は元の coslice の単体と同じ。
使われ方：比較射の次数ごとの逆写像。 -/
def kanNerveUnderInverseSimplex {n : ℕ} (σ : (sliceUnder (nervePoint c)) _⦋n⦌) :
    ComposableArrows (Under c) n :=
  kanNerveUnderChainInverse c (kanNerveUnderUnderlyingChain c σ)
    (kanNerveUnderUnderlyingChain_first c σ)

/-- 概要：復元した Under の単体を比較射で写すと元の単体になる。
方針：射列の右逆性と再表示の公式を使う。
規約：全ての単体についての等式。
使われ方：比較射の全射性。 -/
lemma kanNerveUnderSimplex_inverse {n : ℕ} (σ : (sliceUnder (nervePoint c)) _⦋n⦌) :
    kanNerveUnderSimplex c (kanNerveUnderInverseSimplex c σ) = σ := by
  apply Subtype.ext
  change (pointJoinStdSimplexIso n).hom ≫ (SSet.yonedaEquiv (X := nerve C)).symm
    (kanNerveUnderChain c (kanNerveUnderChainInverse c (kanNerveUnderUnderlyingChain c σ) _)) = _
  rw [kanNerveUnderChain_chainInverse]
  exact kanNerveUnderUnderlyingChain_encode c σ

/-- 概要：比較射で写した単体から元の Under の単体を回収する。
方針：Yoneda の逆性と射列の左逆性を使う。
規約：射列の先頭の等式の証明は選択によらない。
使われ方：比較射の単射性。 -/
lemma kanNerveUnderInverse_simplex {n : ℕ} (F : ComposableArrows (Under c) n) :
    kanNerveUnderInverseSimplex c (kanNerveUnderSimplex c F) = F := by
  have he : kanNerveUnderUnderlyingChain c (kanNerveUnderSimplex c F) = kanNerveUnderChain c F := by
    simp only [kanNerveUnderUnderlyingChain, kanNerveUnderSimplex, Iso.inv_hom_id_assoc,
      Equiv.apply_symm_apply]
  dsimp only [kanNerveUnderInverseSimplex]
  simp only [he]
  exact kanNerveUnderChainInverse_chain c F

/-- 概要：比較射は各次数で全単射を与える。
方針：証明済みの二つの逆性をまとめる。
規約：順方向は元の比較射の成分。
使われ方：全体の同型性の証明。 -/
def kanNerveUnderObjEquiv (n : ℕ) : (nerve (Under c)) _⦋n⦌ ≃ (sliceUnder (nervePoint c)) _⦋n⦌ where
  toFun := kanNerveUnderSimplex c
  invFun := kanNerveUnderInverseSimplex c
  left_inv := kanNerveUnderInverse_simplex c
  right_inv := kanNerveUnderSimplex_inverse c

/-- 概要：通常の Under の nerve からの比較射は同型。
方針：全次数での全単射性を使う。
規約：始対象性などの追加の仮定は不要。
使われ方：native な coslice の古典模型。 -/
instance kanNerveUnderMap_isIso : IsIso (kanNerveUnderMap c) := by
  apply (NatTrans.isIso_iff_isIso_app _).2
  rintro ⟨⟨n⟩⟩
  exact (isIso_iff_bijective _).2 (kanNerveUnderObjEquiv c n).bijective

/-- 概要：通常の Under の nerve と native な coslice の指定同型。
方針：元の比較射とその同型性をまとめる。
規約：順方向は kanNerveUnderMap。
使われ方：右 Kan の局所添字と図式の照合。 -/
def kanNerveUnderIso : nerve (Under c) ≅ sliceUnder (nervePoint c) := asIso (kanNerveUnderMap c)

end SerrePositivity.InfinityCategories.F1B
