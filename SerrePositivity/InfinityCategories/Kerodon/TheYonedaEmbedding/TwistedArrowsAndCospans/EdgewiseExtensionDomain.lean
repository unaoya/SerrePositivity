module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseStandardSimplex

/-!
概要：edgewise の右射影の境界延長に用いる標準単体の部分複体。
方針：右半分の面と、対応する左右二頂点を同時に欠く全ての面の和を取る。
規約：左右の対応は左側の順序を反転させる。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、Corollary 8.1.1.13（Tag 048H）、反転比較の有限な充填領域。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：重みの標準単体表示において添字 i に対応する左頂点。
方針：左因子の反転を頂点番号 n-i で表す。
規約：全体の次数は n+n+1。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、edgewise の面で欠ける左頂点。 -/
def edgewiseLeftVertex (n : ℕ) (i : Fin (n + 1)) : Fin (n + n + 1 + 1) :=
  ⟨n - i.val, by omega⟩

/-- 概要：重みの標準単体表示において添字 i に対応する右頂点。
方針：右因子の頂点番号を n+1 だけずらす。
規約：左頂点と右頂点は同じ添字 i で対にする。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、edgewise の面で欠ける右頂点。 -/
def edgewiseRightVertex (n : ℕ) (i : Fin (n + 1)) : Fin (n + n + 1 + 1) :=
  ⟨n + 1 + i.val, by omega⟩

/-- 概要：重みの右因子の標準単体を構成する頂点集合。
方針：頂点番号が n より大きいものを取る。
規約：添字の全体は Fin(n+n+2)。
使われ方：Kerodon Notation 8.1.1.6（Tag 03JK）、右射影で固定する面。 -/
def edgewiseRightVertices (n : ℕ) : Finset (Fin (n + n + 1 + 1)) :=
  Finset.univ.filter (fun v ↦ n < v.val)

/-- 概要：右半分と、対応する左右二頂点を欠く全ての面を含む部分複体。
方針：右側の全面と edgewise の境界の各面の頂点集合を和でまとめる。
規約：この定義だけから包含の anodyne 性は主張しない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、右射影の境界充填を行う領域。 -/
def edgewiseRightExtensionDomain (n : ℕ) : (Δ[n + n + 1] : SSet.{u}).Subcomplex :=
  stdSimplex.face (edgewiseRightVertices n) ⊔
    ⨆ i : Fin (n + 1), stdSimplex.face ({edgewiseLeftVertex n i, edgewiseRightVertex n i}ᶜ)

/-- 概要：延長領域への単体の所属は右半分への所属または欠ける一対の存在で特徴付く。
方針：部分複体の和と面の所属条件を頂点で計算する。
規約：退化単体も含めて任意の次数 d を扱う。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、欠ける単体の pairing の判定条件。 -/
lemma mem_edgewiseRightExtensionDomain_iff {n d : ℕ}
    (s : (Δ[n + n + 1] : SSet.{u}) _⦋d⦌) :
    s ∈ (edgewiseRightExtensionDomain n).obj (Opposite.op ⦋d⦌) ↔
      (∀ j : Fin (d + 1), n < (s j).val) ∨
        ∃ i : Fin (n + 1), ∀ j : Fin (d + 1),
          s j ≠ edgewiseLeftVertex n i ∧ s j ≠ edgewiseRightVertex n i := by
  change s ∈ (stdSimplex.face (edgewiseRightVertices n)).obj _ ∨
    s ∈ (⨆ i : Fin (n + 1), stdSimplex.face
      ({edgewiseLeftVertex n i, edgewiseRightVertex n i}ᶜ)).obj _ ↔ _
  simp only [
    Subfunctor.iSup_obj, Set.mem_iUnion, stdSimplex.mem_face_iff,
    edgewiseRightVertices, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]

/-- 概要：左右の対応する二頂点は異なる。
方針：左側の番号は n 以下、右側は n より大きいことを使う。
規約：n=0 も含む。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、欠ける二頂点の面の余次元の確認。 -/
lemma edgewiseLeftVertex_ne_right (n : ℕ) (i j : Fin (n + 1)) :
    edgewiseLeftVertex n i ≠ edgewiseRightVertex n j := by
  intro h
  have hv := congrArg Fin.val h
  dsimp [edgewiseLeftVertex, edgewiseRightVertex] at hv
  omega

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
