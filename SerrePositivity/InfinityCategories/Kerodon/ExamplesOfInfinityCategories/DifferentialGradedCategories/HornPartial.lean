module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornComponents
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Residual

/-! # ホーンから回収した既知成分のデータ

概要：未知の二成分を零としておいた成分族を作り、利用可能な面への制限を検証する。
方針：既知成分の回収と面の選択独立性を使う。
規約：HA Proposition 1.3.1.10。未知の二成分は後で充填の解に置き換える。
使われ方：既知の部分集合に関する単体の方程式の検証。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：ホーンから既知の対象と成分を回収し、未知の二成分を零とした単体データ。
方針：全体集合と欠けた面を除いた集合に既知成分の回収を適用する。
規約：HA Proposition 1.3.1.10。使われ方：充填の前の既知の射族。 -/
def knownData {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2) where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.vertexObj σ
  hom I a b k hI ha hb hk :=
    if hf : I ≠ Finset.univ then
      if hm : I ≠ Finset.univ.erase i then _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.recoverHom σ I a b k hI ha hb hk hf hm else 0
    else 0

/-- 概要：利用可能な面の像の部分集合は、未知の二集合のいずれでもない。
方針：その面が飛ばす頂点を像が含まないことから、面の存在の特徴づけを使う。
規約：HA Proposition 1.3.1.10。使われ方：面上の既知成分の計算の分岐。 -/
lemma image_known {n : ℕ} {i : Fin (n + 3)} (j : Fin (n + 3)) (hji : j ≠ i)
    (J : Finset (Fin (n + 2))) :
    J.image j.succAbove ≠ Finset.univ ∧ J.image j.succAbove ≠ Finset.univ.erase i := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.exists_covering_face _ i).mp
  refine ⟨j, hji, ?_⟩
  rintro hj
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hj
  exact Fin.succAbove_ne j x hx

/-- 概要：既知データの各面の像の成分は、元のホーン面の成分と異種等号で一致する。
方針：像が既知であることから条件分岐を簡約し、回収の面との一致を使う。
規約：HA Proposition 1.3.1.10。使われ方：データ全体の面への制限の検証。 -/
lemma knownData_hom_heq_face {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (j : Fin (n + 3)) (hji : j ≠ i) (J : Finset (Fin (n + 2)))
    (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    HEq (((knownData σ).pullback j.succAboveOrderEmb.toOrderHom).hom J a b k hJ ha hb hk)
      ((σ.app _ (SSet.horn.face i j hji)).hom J a b k hJ ha hb hk) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
    j.succAboveOrderEmb.injective.injOn]
  have hf : J.image j.succAboveOrderEmb.toOrderHom ≠ Finset.univ := (image_known j hji J).1
  have hm : J.image j.succAboveOrderEmb.toOrderHom ≠ Finset.univ.erase i := (image_known j hji J).2
  simp only [knownData, dite_eq_left hf, dite_eq_left hm]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.recoverHom_heq_face σ
  rfl

/-- 概要：既知データを利用可能な任意の面に制限すると、元のホーン面のデータに等しい。
方針：頂点の一致と各成分の異種等号での一致から、データの外延性を使う。
規約：HA Proposition 1.3.1.10。使われ方：既知の全ての方程式の面からの回収。 -/
lemma knownData_pullback_face {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (j : Fin (n + 3)) (hji : j ≠ i) :
    (knownData σ).pullback j.succAboveOrderEmb.toOrderHom =
      (σ.app _ (SSet.horn.face i j hji)).toSimplexData := by
  have hobj : ((knownData σ).pullback j.succAboveOrderEmb.toOrderHom).obj =
      (σ.app _ (SSet.horn.face i j hji)).obj := by
    funext k
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.face_obj σ j hji k).symm
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  exact knownData_hom_heq_face σ j hji

/-- 概要：既知データは、利用可能な面に含まれる部分集合について単体の方程式を満たす。
方針：面への引き戻しが元の単体データであることと、単射による右辺の移送を使う。
規約：HA Proposition 1.3.1.10。使われ方：既知方程式の一般の部分集合への移送。 -/
lemma knownData_equation_image {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (j : Fin (n + 3)) (hji : j ≠ i) (J : Finset (Fin (n + 2)))
    (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    differential A ((knownData σ).hom (J.image j.succAbove) (j.succAbove a) (j.succAbove b) k
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two j.succAboveOrderEmb.injective.injOn hJ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min (f := j.succAbove) j.succAboveOrderEmb.monotone
        (by rw [ha]; exact J.isLeast_min' _) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max (f := j.succAbove) j.succAboveOrderEmb.monotone
        (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective J
              (show Function.Injective j.succAbove from j.succAboveOrderEmb.injective)]
          exact hk)) =
    (knownData σ).rhs (J.image j.succAbove) (j.succAbove a) (j.succAbove b) k
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two j.succAboveOrderEmb.injective.injOn hJ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min (f := j.succAbove) j.succAboveOrderEmb.monotone
        (by rw [ha]; exact J.isLeast_min' _) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max (f := j.succAbove) j.succAboveOrderEmb.monotone
        (by rw [hb]; exact J.isGreatest_max' _) _)
      (by rw [Finset.card_image_of_injective J
              (show Function.Injective j.succAbove from j.succAboveOrderEmb.injective)]
          exact hk) := by
  have hh := (σ.app _ (SSet.horn.face i j hji)).equation J a b k hJ ha hb hk
  rw [← knownData_pullback_face σ j hji] at hh
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullback_rhs_of_inj _ _ _ _ _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn] at hh
  exact hh

/-- 概要：既知データは、全体集合と欠けた面以外の全ての部分集合で単体の方程式を満たす。
方針：その集合を含む面を選び、面の逆像の方程式を端点と次数とともに戻す。
規約：HA Proposition 1.3.1.10。使われ方：充填の検証で残る方程式を未知の二成分に限定する。 -/
lemma knownData_equation {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (I : Finset (Fin (n + 3))) (a b : Fin (n + 3)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hfull : I ≠ Finset.univ) (hmissing : I ≠ Finset.univ.erase i) :
    differential A ((knownData σ).hom I a b k hI ha hb hk) =
      (knownData σ).rhs I a b k hI ha hb hk := by
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace I i hfull hmissing
  have hji : j ≠ i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_ne I i hfull hmissing
  have hj : j ∉ I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_notMem I i hfull hmissing
  let J := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn
  have hcard : J.card = I.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_preimage I j hj
  have hJ : 2 ≤ J.card := by omega
  have hImage : J.image j.succAbove = I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage I j hj
  let a' := J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  let b' := J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  have ha' : j.succAbove a' = a := by
    rw [ha]
    simpa only [hImage] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min (f := j.succAbove) j.succAboveOrderEmb.monotone
      (J.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _)
  have hb' : j.succAbove b' = b := by
    rw [hb]
    simpa only [hImage] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max (f := j.succAbove) j.succAboveOrderEmb.monotone
      (J.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (Finset.Nonempty.image (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ) _)
  have hh := knownData_equation_image σ j hji J a' b' k hJ rfl rfl (by rw [hcard]; exact hk)
  cases ha'
  cases hb'
  simpa only [hImage] using hh

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial
