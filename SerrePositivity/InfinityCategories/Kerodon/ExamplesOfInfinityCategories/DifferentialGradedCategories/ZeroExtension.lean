module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ZeroFunctor

/-! # 零複体を最後の頂点として加える直接の単体拡張

概要：任意の複体 dg nerve の単体に零頂点を追加する。
方針：最後の退化を二相の零自然変換で写し、全単体方程式を既存の成分計算で保つ。
規約：HTT §1.2.12、HA Construction 1.3.1.6。使われ方：N7b の零終対象の境界充填。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Limits DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：最後の頂点だけを一相にし、全先頭頂点を零相にする単調写像。
方針：最終点に等しいかどうかで場合分けする。
規約：HA Construction 1.3.1.6。使われ方：零頂点を最後に加える二相の指定。 -/
def terminalPhase (n : ℕ) : Fin (n + 2) →o Fin 2 where
  toFun i := if i = Fin.last (n + 1) then 1 else 0
  monotone' := by
    intro i j hij
    dsimp only
    split_ifs with hi hj hj
    · exact le_rfl
    · exact False.elim (hj (le_antisymm (Fin.le_last _) (hi ▸ hij)))
    · exact Fin.zero_le _
    · exact le_rfl

/-- 概要：全先頭頂点の相は零。
方針：castSucc は最終点に等しくないことを使う。
規約：HA Construction 1.3.1.6。使われ方：元の単体を先頭面に保つ。 -/
lemma terminalPhase_castSucc (n : ℕ) (i : Fin (n + 1)) : terminalPhase n i.castSucc = 0 := by
  simp only [terminalPhase, OrderHom.coe_mk, ite_eq_right (ne_of_lt (Fin.castSucc_lt_last i))]

/-- 概要：最後に追加した頂点の相は一。
方針：最終点の真の分岐を評価する。
規約：HA Construction 1.3.1.6。使われ方：追加した頂点を零複体にする。 -/
lemma terminalPhase_last (n : ℕ) : terminalPhase n (Fin.last (n + 1)) = 1 := by
  simp only [terminalPhase, OrderHom.coe_mk, ite_true]

/-- 概要：任意の単体を先頭面とし、零複体を最後の頂点とする単体。
方針：最後の頂点の退化を恒等から零定値への自然変換の二相の単体で写す。
規約：HTT §1.2.12、N7b。使われ方：境界に与えられた先頭面の直接の拡張。 -/
def appendZero (Z : Complex A) (hZ : IsZero Z) {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toZeroStrict Z hZ).simplex (s.pullback (Fin.last n).predAboveOrderHom) (terminalPhase n)

/-- 概要：追加した最後の頂点は零複体そのもの。
方針：一相では零定値関手の対象を返すことを評価する。
規約：HTT §1.2.12。使われ方：零終対象の端点条件。 -/
lemma appendZero_last (Z : Complex A) (hZ : IsZero Z) {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) :
    (appendZero Z hZ s).obj (Fin.last (n + 1)) = Z := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj (DGFunctor.id (Complex A)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.constantZeroFunctor Z hZ)
    (terminalPhase n (Fin.last (n + 1))) _ = Z
  rw [terminalPhase_last]
  rfl

/-- 概要：零頂点を追加した単体の先頭面は元の単体。
方針：二相構成の自然性を使い、全先頭相が零かつ退化の先頭制限が恒等であることを計算する。
規約：HTT §1.2.12、HA Construction 1.3.1.6。使われ方：境界の先頭面との一致。 -/
lemma appendZero_front (Z : Complex A) (hZ : IsZero Z) {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) :
    (appendZero Z hZ s).pullback Fin.castSuccOrderEmb.toOrderHom = s := by
  unfold appendZero
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.simplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp]
  have hphase : (terminalPhase n).comp Fin.castSuccOrderEmb.toOrderHom =
      OrderHom.const _ (0 : Fin 2) := by
    apply DFunLike.ext
    intro i
    exact terminalPhase_castSucc n i
  have hindex : (Fin.last n).predAboveOrderHom.comp Fin.castSuccOrderEmb.toOrderHom =
      OrderHom.id := by
    apply DFunLike.ext
    intro i
    exact Fin.predAbove_last_castSucc
  rw [hphase, hindex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_id, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplex_zero]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_id s.toSimplexData

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
