module
public import SerrePositivity.InfinityCategories.DGNerve.PinchedReconstructData
public import SerrePositivity.InfinityCategories.DGNerve.PinchedFront

/-! # 再構成データの先頭面

概要：線形族から再構成したデータの先頭面が定値面であることを示す。
方針：単射な先頭埋め込みの引き戻しを計算し、二点は単位、高次は零として比較する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：逆構成の端点条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：再構成データの先頭面は x の定値単体のデータ。
方針：対象と各成分を比較し、単位・零の二分岐を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：右 pinched 条件の先頭面。 -/
lemma toSimplexData_front {n : ℕ} (f : LinearData A x y n) :
    f.toSimplexData.pullback Fin.castSuccOrderEmb.toOrderHom =
      (InfinityCategories.PinchedHom.constant (X := dgNerve A D)
        (Simplex.vertex x) n).toSimplexData := by
  have ho : (f.toSimplexData.pullback Fin.castSuccOrderEmb.toOrderHom).obj =
      (InfinityCategories.PinchedHom.constant (X := dgNerve A D) (Simplex.vertex x) n).obj := by
    funext i
    exact reconstructObj_castSucc x y i
  apply SimplexData.ext ho
  apply HomFamily.heq_of_pointwise ho
  intro J a b k hJ ha hb hk
  let α : Fin (n + 1) →o Fin (n + 2) := Fin.castSuccOrderEmb.toOrderHom
  have hi : Set.InjOn α (J : Set (Fin (n + 1))) := (Fin.castSucc_injective _).injOn
  have hcard : (J.image α).card = J.card := Finset.card_image_of_injOn hi
  have ham := J.isLeast_min' (Index.nonempty hJ)
  have hbm := J.isGreatest_max' (Index.nonempty hJ)
  rw [SimplexData.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  by_cases hc : J.card = 2
  · have hf := f.toSimplexData_hom_unit (J.image α) (α a) (α b) k (Index.image_two hi hJ)
      (Index.image_min α.monotone (by rw [ha]; exact ham) _)
      (Index.image_max α.monotone (by rw [hb]; exact hbm) _)
      (by rw [hcard]; exact hk) (ne_of_lt (Fin.castSucc_lt_last b)) (by rw [hcard]; exact hc)
    exact hf.trans (constant_hom_unit x J a b k hJ ha hb hk hc).symm
  · have hf := f.toSimplexData_hom_zero (J.image α) (α a) (α b) k (Index.image_two hi hJ)
      (Index.image_min α.monotone (by rw [ha]; exact ham) _)
      (Index.image_max α.monotone (by rw [hb]; exact hbm) _)
      (by rw [hcard]; exact hk) (ne_of_lt (Fin.castSucc_lt_last b)) (by rw [hcard]; exact hc)
    rw [hf, constant_hom_zero x J a b k hJ ha hb hk hc]
    change HEq (0 : GradedHom A (reconstructObj x y a.castSucc) (reconstructObj x y b.castSucc) k)
      (0 : GradedHom A x x k)
    rw [reconstructObj_castSucc, reconstructObj_castSucc]

/-- 概要：再構成データの最終頂点は y の零単体のデータ。
方針：最終対象を評価し、零単体の射族の一意性を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5。使われ方：右 pinched 条件の終端。 -/
lemma toSimplexData_last {n : ℕ} (f : LinearData A x y n) :
    f.toSimplexData.pullback (InfinityCategories.PinchedHom.lastVertex n).toOrderHom =
      (Simplex.vertex y).toSimplexData := by
  apply SimplexData.ext
  · funext i
    exact reconstructObj_of_eq_last x y rfl
  · exact zero_hom_heq _ _

end SerrePositivity.InfinityCategories.DGNerve.PinchedHom.LinearData
