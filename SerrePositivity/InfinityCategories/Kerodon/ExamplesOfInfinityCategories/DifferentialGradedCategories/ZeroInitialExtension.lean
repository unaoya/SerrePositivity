module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ZeroExtensionality

/-! # 零複体を最初の頂点として加える単体拡張

概要：任意の複体 dg nerve の単体に零頂点を先頭へ加える。
方針：最初の退化を零定値から恒等への厳密自然変換で写す。
規約：HTT §1.2.12 の双対、HA Construction 1.3.1.6。使われ方：N7b の零始対象。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Limits DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：最初の頂点だけを零相にし、残りを一相にする単調写像。
方針：最初の頂点に等しいかどうかで場合分けする。
規約：HA Construction 1.3.1.6。使われ方：零頂点を先頭へ加える二相の指定。 -/
def initialPhase (n : ℕ) : Fin (n + 2) →o Fin 2 where
  toFun i := if i = 0 then 0 else 1
  monotone' := by
    intro i j hij
    dsimp only
    split_ifs with hi hj hj
    · exact le_rfl
    · exact Fin.zero_le _
    · exact False.elim (hi (le_antisymm (hj ▸ hij) (Fin.zero_le i)))
    · exact le_rfl

/-- 概要：全ての後続頂点の相は一。
方針：succ は零でないことを使う。
規約：HA Construction 1.3.1.6。使われ方：元の単体を後続面に保つ。 -/
lemma initialPhase_succ (n : ℕ) (i : Fin (n + 1)) : initialPhase n i.succ = 1 := by
  simp only [initialPhase, OrderHom.coe_mk, ite_eq_right (Fin.succ_ne_zero i)]

/-- 概要：追加する先頭頂点の相は零。
方針：真の条件分岐を評価する。
規約：HA Construction 1.3.1.6。使われ方：追加した頂点を零複体にする。 -/
lemma initialPhase_zero (n : ℕ) : initialPhase n 0 = 0 := by
  simp only [initialPhase, OrderHom.coe_mk, ite_true]

/-- 概要：任意の単体を後続面とし、零複体を最初の頂点とする単体。
方針：最初の頂点の退化を零定値から恒等への自然変換の二相の単体で写す。
規約：HTT §1.2.12 の双対、N7b。使われ方：零始対象の境界充填。 -/
def prependZero (Z : Complex A) (hZ : IsZero Z) {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n + 1) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fromZeroStrict Z hZ).simplex (s.pullback (0 : Fin (n + 1)).predAboveOrderHom) (initialPhase n)

/-- 概要：追加した最初の頂点は零複体そのもの。
方針：零相では零定値関手の対象を返すことを評価する。
規約：HTT §1.2.12 の双対。使われ方：零始対象の端点条件。 -/
lemma prependZero_first (Z : Complex A) (hZ : IsZero Z) {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) :
    (prependZero Z hZ s).obj 0 = Z := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.phaseObj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.constantZeroFunctor Z hZ) (DGFunctor.id (Complex A))
    (initialPhase n 0) ((s.pullback (0 : Fin (n + 1)).predAboveOrderHom).obj 0) = Z
  rw [initialPhase_zero]
  rfl

/-- 概要：零頂点を加えた単体の後続面は元の単体。
方針：二相構成の自然性を使い、全後続相が一で退化の後続制限が恒等であることを使う。
規約：HTT §1.2.12 の双対。使われ方：指定境界の後続面との一致。 -/
lemma prependZero_back (Z : Complex A) (hZ : IsZero Z) {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n) :
    (prependZero Z hZ s).pullback (Fin.succOrderEmb (n + 1)).toOrderHom = s := by
  unfold prependZero
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans.simplex_pullback, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_comp]
  have hphase : (initialPhase n).comp (Fin.succOrderEmb (n + 1)).toOrderHom =
      OrderHom.const _ (1 : Fin 2) := by
    apply DFunLike.ext
    intro i
    exact initialPhase_succ n i
  have hindex : (0 : Fin (n + 1)).predAboveOrderHom.comp (Fin.succOrderEmb (n + 1)).toOrderHom =
      OrderHom.id := by
    apply DFunLike.ext
    intro i
    exact Fin.predAbove_zero_succ
  rw [hphase, hindex, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Pullback.pullback_id, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplex_one]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_id s.toSimplexData

/-- 概要：零始域を持つ単体は後続面で決まる。
方針：最初の頂点を使う成分は零、残りは後続面の単射な成分として比較する。
規約：HTT §1.2.12 の双対。使われ方：零始対象の全境界との一致。 -/
lemma Simplex.ext_of_zero_first (Z : Complex A) (hZ : IsZero Z) {n : ℕ}
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) (n + 1))
    (hf : s.pullback (Fin.succOrderEmb (n + 1)).toOrderHom =
      t.pullback (Fin.succOrderEmb (n + 1)).toOrderHom)
    (hs : s.obj 0 = Z) (ht : t.obj 0 = Z) : s = t := by
  have hobj : s.obj = t.obj := by
    funext i
    induction i using Fin.cases with
    | zero => exact hs.trans ht.symm
    | succ i => exact congrArg (fun a : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (Complex A) n => a.obj i) hf
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro I a b k hI ha hb hk
  by_cases haZero : a = 0
  · subst haZero
    have hs0 : s.hom I 0 b k hI ha hb hk = 0 :=
      homogeneous_eq_zero_of_isZero_src (hs.symm ▸ hZ) _
    have ht0 : t.hom I 0 b k hI ha hb hk = 0 :=
      homogeneous_eq_zero_of_isZero_src (ht.symm ▸ hZ) _
    rw [hs0, ht0]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zeroGradedHom_heq (congrFun hobj 0) (congrFun hobj b) k
  · have haMin : IsLeast (I : Set (Fin (n + 2))) a := by
      rw [ha]
      exact I.isLeast_min' _
    have hzero : (0 : Fin (n + 2)) ∉ I := by
      intro h
      exact haZero (le_antisymm (haMin.2 h) (Fin.zero_le a))
    let α : Fin (n + 1) →o Fin (n + 2) := (Fin.succOrderEmb (n + 1)).toOrderHom
    let J := I.preimage α (Fin.succ_injective _).injOn
    have hImage : J.image α = I := by
      change (I.preimage Fin.succ _).image Fin.succ = I
      simpa only [Fin.succAbove_zero] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage I 0 hzero
    have hcard : J.card = I.card := by
      rw [← hImage, Finset.card_image_of_injOn
        (show Set.InjOn α (J : Set (Fin (n + 1))) from (Fin.succ_injective _).injOn)]
    have hJ : 2 ≤ J.card := by omega
    let a' := J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
    let b' := J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
    have ha' : α a' = a := by
      rw [ha]
      simpa only [hImage] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone
        (J.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _)
    have hb' : α b' = b := by
      rw [hb]
      simpa only [hImage] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone
        (J.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _)
    have H := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.hom_heq_of_pullback_eq s t α α hf J a' b' k hJ rfl rfl
      (by rw [hcard]; exact hk) (Fin.succ_injective _).injOn (Fin.succ_injective _).injOn
    cases ha'
    cases hb'
    simpa only [hImage] using H

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
