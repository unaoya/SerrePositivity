module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinPointIndex
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeFamilyPureHom
/-!
概要：パラメーターの一点削除を標準面へ戻し、定値側の成分を単位・零へ同定する。
方針：昇順列挙の一意性と、既存の定値 dg nerve 単体の成分公式を使う。
規約：終点は任意の実頂点として扱う。
使われ方：混合 HA のパラメーター側を余錐族の標準面の和へ直す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial

lemma dgCoherentBarErase_orderHom (n : ℕ) (j : Fin (n + 2)) :
    SimplexCategory.mkHom
      (((Finset.univ : Finset (Fin (n + 2))).erase j).orderEmbOfFin (by simp)).toOrderHom =
      SimplexCategory.δ j := by
  have he : (j.succAboveOrderEmb : Fin (n + 1) → Fin (n + 2)) =
      ((Finset.univ : Finset (Fin (n + 2))).erase j).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique (by simp)
      (fun i => Finset.mem_erase.mpr ⟨Fin.succAbove_ne j i, Finset.mem_univ _⟩)
      j.succAboveOrderEmb.strictMono
  ext i : 3
  exact congrFun he.symm i

lemma dgCoherentBarUniv_erase_last (m : ℕ) :
    (Finset.univ : Finset (Fin (m + 2))).erase (Fin.last (m + 1)) =
      Finset.univ.filter (· ≤ (Fin.last m).castSucc) := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_filter, true_and,
    ne_eq, Fin.ext_iff, Fin.le_def, Fin.val_last, Fin.val_castSucc]
  have := x.isLt
  omega

variable {R : Type u} [CommRing R] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]

lemma dgCoherentBarConstant_hom_zero (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) _⦋0⦌) {n : ℕ}
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hc : J.card ≠ 2) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n).hom J a b k hJ ha hb hk)
      (0 : GradedHom R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R C y) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R C y) k) := by
  obtain ⟨N, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R C).symm.surjective y
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_hom_zero N J a b k hJ ha hb hk hc)

lemma dgCoherentBarConstant_hom_unit (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R C) _⦋0⦌) {n : ℕ}
    (J : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) (hc : J.card = 2) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n).hom J a b k hJ ha hb hk)
      (unitElement R (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R C y)).val := by
  obtain ⟨N, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve.vertexEquiv R C).symm.surjective y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.constant_hom_unit N J a b k hJ ha hb hk hc

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
