module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedReconstructData
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedFront

/-! # 再構成データの先頭面

概要：線形族から再構成したデータの先頭面が定値面であることを示す。
方針：単射な先頭埋め込みの引き戻しを計算し、二点は単位、高次は零として比較する。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：逆構成の端点条件。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

open CategoryTheory DifferentialGraded

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 概要：再構成データの先頭面は x の定値単体のデータ。
方針：対象と各成分を比較し、単位・零の二分岐を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：右 pinched 条件の先頭面。 -/
lemma toSimplexData_front {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) :
    f.toSimplexData.pullback Fin.castSuccOrderEmb.toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).toSimplexData := by
  have ho : (f.toSimplexData.pullback Fin.castSuccOrderEmb.toOrderHom).obj =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) n).obj := by
    funext i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.reconstructObj_castSucc x y i
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext ho
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise ho
  intro J a b k hJ ha hb hk
  let α : Fin (n + 1) →o Fin (n + 2) := Fin.castSuccOrderEmb.toOrderHom
  have hi : Set.InjOn α (J : Set (Fin (n + 1))) := (Fin.castSucc_injective _).injOn
  have hcard : (J.image α).card = J.card := Finset.card_image_of_injOn hi
  have ham := J.isLeast_min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  have hbm := J.isGreatest_max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi]
  by_cases hc : J.card = 2
  · have hf := f.toSimplexData_hom_unit (J.image α) (α a) (α b) k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hJ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (by rw [ha]; exact ham) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (by rw [hb]; exact hbm) _)
      (by rw [hcard]; exact hk) (ne_of_lt (Fin.castSucc_lt_last b)) (by rw [hcard]; exact hc)
    exact hf.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_hom_unit x J a b k hJ ha hb hk hc).symm
  · have hf := f.toSimplexData_hom_zero (J.image α) (α a) (α b) k (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_two hi hJ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (by rw [ha]; exact ham) _)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (by rw [hb]; exact hbm) _)
      (by rw [hcard]; exact hk) (ne_of_lt (Fin.castSucc_lt_last b)) (by rw [hcard]; exact hc)
    rw [hf, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_hom_zero x J a b k hJ ha hb hk hc]
    change HEq (0 : GradedHom A (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.reconstructObj x y a.castSucc) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.reconstructObj x y b.castSucc) k)
      (0 : GradedHom A x x k)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.reconstructObj_castSucc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.reconstructObj_castSucc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (toSimplexData_front)


/-- 概要：再構成データの最終頂点は y の零単体のデータ。
方針：最終対象を評価し、零単体の射族の一意性を使う。
規約：HA Construction 1.3.1.6、Kerodon §4.6.5（Tag 01KW）。使われ方：右 pinched 条件の終端。 -/
lemma toSimplexData_last {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n) :
    f.toSimplexData.pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).toOrderHom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y).toSimplexData := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · funext i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.reconstructObj_of_eq_last x y rfl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_hom_heq _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces (toSimplexData_last)


end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
