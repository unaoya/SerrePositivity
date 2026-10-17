module
public import SerrePositivity.InfinityCategories.DGNerve.PinchedDataFront
public import SerrePositivity.InfinityCategories.DGNerve.PinchedTerms

/-! # 方程式を課す前の右 pinched データの切断合成

概要：右 pinched の端点条件だけから全ての削除項と切断合成を回収族に比較する。
方針：先頭面の単位・零と有限集合の切断の計算を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：逆構成の方程式の線形化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data

open CategoryTheory DifferentialGraded
open scoped Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：二番目以外の内部先頭点での切断合成は零。
方針：左切断が三点以上であることを判定し、先頭面の高次成分を零にする。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：線形化で唯一の単位の合成項を残す。 -/
lemma cutComposite_zero_of_ne_second {n : ℕ} (s : Data A D x y n)
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ J) (haj : J.min' (Index.nonempty hJ) < j)
    (hne : j ≠ second J hJ) :
    s.val.cutComposite (withLast J) (J.min' (Index.nonempty hJ)).castSucc
      (Fin.last (n + 1)) k (two_withLast (Index.nonempty hJ))
      (min_withLast (Index.nonempty hJ) _) (max_withLast J _) (by rw [card_withLast]; omega)
      j.castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
      (Fin.castSucc_lt_castSucc_iff.mpr haj) (Fin.castSucc_lt_last j) = 0 := by
  have hL := Index.left_two (J.min'_mem (Index.nonempty hJ)) hj haj
  have haL := Index.left_min (J.isLeast_min' (Index.nonempty hJ)) haj.le (Index.nonempty hL)
  have hjL := Index.left_max hj (Index.nonempty hL)
  have hc : (J.filter (· ≤ j)).card ≠ 2 := mt (left_card_two_iff J hJ j hj haj).mp hne
  dsimp only [SimplexData.cutComposite, SimplexData.cutLeft]
  have hz : ∀ (hI : 2 ≤ ((withLast J).filter (· ≤ j.castSucc)).card)
      (ha : (J.min' (Index.nonempty hJ)).castSucc =
        ((withLast J).filter (· ≤ j.castSucc)).min' (Index.nonempty hI))
      (hb : j.castSucc = ((withLast J).filter (· ≤ j.castSucc)).max' (Index.nonempty hI)),
      s.val.hom ((withLast J).filter (· ≤ j.castSucc))
        (J.min' (Index.nonempty hJ)).castSucc j.castSucc
        (2 - (((withLast J).filter (· ≤ j.castSucc)).card : ℤ)) hI ha hb rfl = 0 := by
    intro hI ha hb
    exact front_hom_zero_of_image s _ _ _ _ _ hI ha hb rfl hL haL hjL (left_withLast J j) hc
  rw [hz]
  exact compose_zero _ _

/-- 概要：二番目の先頭点での切断合成は右切断成分と異種等号で一致する。
方針：左切断の濃度が二であることと先頭面の単位の同定を通常順の単位則に適用する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：最小点の削除成分の復元。 -/
lemma cutComposite_second {n : ℕ} (s : Data A D x y n)
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    HEq (s.val.cutComposite (withLast J) (J.min' (Index.nonempty hJ)).castSucc
      (Fin.last (n + 1)) k (two_withLast (Index.nonempty hJ))
      (min_withLast (Index.nonempty hJ) _) (max_withLast J _) (by rw [card_withLast]; omega)
      (second J hJ).castSucc
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨_, (Finset.mem_erase.mp (second_mem_erase J hJ)).2, rfl⟩))
      (Fin.castSucc_lt_castSucc_iff.mpr (first_lt_second J hJ))
      (Fin.castSucc_lt_last _))
      (s.val.cutRight (withLast J) (Fin.last (n + 1))
        (two_withLast (Index.nonempty hJ)) (max_withLast J _) (second J hJ).castSucc
        (Finset.mem_insert_of_mem (Finset.mem_image.mpr
          ⟨_, (Finset.mem_erase.mp (second_mem_erase J hJ)).2, rfl⟩))
        (Fin.castSucc_lt_last _)) := by
  have hj := (Finset.mem_erase.mp (second_mem_erase J hJ)).2
  have haj := first_lt_second J hJ
  have hL := Index.left_two (J.min'_mem (Index.nonempty hJ)) hj haj
  have haL := Index.left_min (J.isLeast_min' (Index.nonempty hJ)) haj.le (Index.nonempty hL)
  have hjL := Index.left_max hj (Index.nonempty hL)
  have hc : (J.filter (· ≤ second J hJ)).card = 2 :=
    (left_card_two_iff J hJ _ hj haj).mpr rfl
  dsimp only [SimplexData.cutComposite]
  apply compose_unit_of_heq
  · exact (source_obj s _).trans (source_obj s _).symm
  · rw [left_withLast, Finset.card_image_of_injective _ (Fin.castSucc_injective _), hc]
    norm_num
  · dsimp only [SimplexData.cutLeft]
    have hu : ∀ (hI : 2 ≤ ((withLast J).filter (· ≤ (second J hJ).castSucc)).card)
        (ha : (J.min' (Index.nonempty hJ)).castSucc =
          ((withLast J).filter (· ≤ (second J hJ).castSucc)).min' (Index.nonempty hI))
        (hb : (second J hJ).castSucc =
          ((withLast J).filter (· ≤ (second J hJ).castSucc)).max' (Index.nonempty hI)),
        HEq (s.val.hom ((withLast J).filter (· ≤ (second J hJ).castSucc))
          (J.min' (Index.nonempty hJ)).castSucc (second J hJ).castSucc
          (2 - (((withLast J).filter (· ≤ (second J hJ).castSucc)).card : ℤ)) hI ha hb rfl)
          (unitElement A x).val := by
      intro hI ha hb
      exact front_hom_unit_of_image s _ _ _ _ _ hI ha hb rfl hL haL hjL
        (left_withLast J _) hc
    refine (hu _ _ _).trans ?_
    rw [source_obj s (second J hJ)]

/-- 概要：二番目の点の右切断成分は、最小点を消した集合の回収成分と異種等号で一致する。
方針：右切断の集合と端点・次数を削除集合に同定し、成分回収の異種等号を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：最初の線形削除項。 -/
lemma cutRight_second_heq_component {n : ℕ} (s : Data A D x y n)
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    HEq (s.val.cutRight (withLast J) (Fin.last (n + 1))
      (two_withLast (Index.nonempty hJ)) (max_withLast J _) (second J hJ).castSucc
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨_, (Finset.mem_erase.mp (second_mem_erase J hJ)).2, rfl⟩)) (Fin.castSucc_lt_last _))
      ((toLinearData s).component (J.erase (J.min' (Index.nonempty hJ))) (k + 1)
        (LinearData.erase_nonempty hJ _ (J.min'_mem _))
        (by have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty hJ)); omega)) := by
  let E := J.erase (J.min' (Index.nonempty hJ))
  have hE : E.Nonempty := LinearData.erase_nonempty hJ _ (J.min'_mem _)
  have hdeg : k + 1 = 1 - (E.card : ℤ) := by
    have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty hJ))
    dsimp only [E]
    omega
  refine HEq.trans ?_ (toLinearData_component_heq s E (k + 1) hE hdeg).symm
  dsimp only [SimplexData.cutRight]
  apply s.val.hom_heq_of_indices_degree
  · rw [right_withLast, right_second]
  · rfl
  · rfl
  · have he : (withLast J).filter ((second J hJ).castSucc ≤ ·) = withLast E := by
      rw [right_withLast, right_second]
    rw [he, card_withLast]
    omega

/-- 概要：二番目での切断合成は最小点を消した集合の回収成分と異種等号で一致する。
方針：単位の合成則と右切断の削除成分への同定を合成する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：非線形項の線形化。 -/
lemma cutComposite_second_heq_component {n : ℕ} (s : Data A D x y n)
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    HEq (s.val.cutComposite (withLast J) (J.min' (Index.nonempty hJ)).castSucc
      (Fin.last (n + 1)) k (two_withLast (Index.nonempty hJ))
      (min_withLast (Index.nonempty hJ) _) (max_withLast J _) (by rw [card_withLast]; omega)
      (second J hJ).castSucc
      (Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨_, (Finset.mem_erase.mp (second_mem_erase J hJ)).2, rfl⟩))
      (Fin.castSucc_lt_castSucc_iff.mpr (first_lt_second J hJ))
      (Fin.castSucc_lt_last _))
      ((toLinearData s).component (J.erase (J.min' (Index.nonempty hJ))) (k + 1)
        (LinearData.erase_nonempty hJ _ (J.min'_mem _))
        (by have := Finset.card_erase_add_one (J.min'_mem (Index.nonempty hJ)); omega)) :=
  (cutComposite_second s J hJ k hk).trans (cutRight_second_heq_component s J hJ k hk)

/-- 概要：内部先頭点の削除成分は、その点を消した集合の回収成分と異種等号で一致する。
方針：削除集合の同定、最小点の保存、次数の濃度計算を成分の比較に適用する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：全ての非最小点の線形削除項。 -/
lemma erasedComponent_heq_component {n : ℕ} (s : Data A D x y n)
    (J : Finset (Fin (n + 1))) (hJ : 2 ≤ J.card) (k : ℤ) (hk : k = 1 - (J.card : ℤ))
    (j : Fin (n + 1)) (hj : j ∈ J) (haj : J.min' (Index.nonempty hJ) < j) :
    HEq (s.val.erasedComponent (withLast J) (J.min' (Index.nonempty hJ)).castSucc
      (Fin.last (n + 1)) k (two_withLast (Index.nonempty hJ))
      (min_withLast (Index.nonempty hJ) _) (max_withLast J _) (by rw [card_withLast]; omega)
      j.castSucc (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩))
      (Fin.castSucc_lt_castSucc_iff.mpr haj) (Fin.castSucc_lt_last j))
      ((toLinearData s).component (J.erase j) (k + 1) (LinearData.erase_nonempty hJ j hj)
        (by have := Finset.card_erase_add_one hj; omega)) := by
  have hE := LinearData.erase_nonempty hJ j hj
  have hdeg : k + 1 = 1 - ((J.erase j).card : ℤ) := by
    have := Finset.card_erase_add_one hj
    omega
  refine HEq.trans ?_ (toLinearData_component_heq s (J.erase j) (k + 1) hE hdeg).symm
  dsimp only [SimplexData.erasedComponent]
  apply s.val.hom_heq_of_indices_degree
  · exact erase_withLast J j
  · exact congrArg Fin.castSucc (Index.erase_min (J.isLeast_min' _) haj _)
  · rfl
  · rfl


end SerrePositivity.InfinityCategories.DGNerve.PinchedHom.Data
