module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinCoordinates
/-!
概要：元の単体とパラメーターの双方の添字写像を、join の全頂点へ延長する。
方針：左右の区間ごとに順序写像を作用させ、既存の連結写像との可換性を示す。
規約：単射性は仮定せず、面と退化を同じ式で扱う。
使われ方：高次余錐族の成分の自然性と退化消滅。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory SSet
open scoped _root_.Simplicial

def dgCoherentBarJoinOrderMap {a b n m : ℕ}
    (α : Fin (a + 1) →o Fin (n + 1)) (β : Fin (b + 1) →o Fin (m + 1)) :
    Fin (a + b + 1 + 1) →o Fin (n + m + 1 + 1) where
  toFun i := if h : i.val < a + 1 then
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m (α ⟨i.val, h⟩)
    else _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m (β ⟨i.val - (a + 1), by have := i.isLt; omega⟩)
  monotone' i j hij := by
    dsimp only
    split_ifs with hi hj hj
    · exact α.monotone hij
    · change (α _).val ≤ n + 1 + (β _).val
      have := (α ⟨i.val, hi⟩).isLt
      omega
    · have : i.val ≤ j.val := hij
      omega
    · exact Nat.add_le_add_left (β.monotone (Nat.sub_le_sub_right hij _)) _

lemma dgCoherentBarJoinOrderMap_left {a b n m : ℕ}
    (α : Fin (a + 1) →o Fin (n + 1)) (β : Fin (b + 1) →o Fin (m + 1))
    (i : Fin (a + 1)) :
    dgCoherentBarJoinOrderMap α β (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft a b i) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m (α i) := by
  simp only [dgCoherentBarJoinOrderMap, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinLeftOrderHom,
    OrderHom.coe_mk, i.isLt,
    dite_true]

lemma dgCoherentBarJoinOrderMap_right {a b n m : ℕ}
    (α : Fin (a + 1) →o Fin (n + 1)) (β : Fin (b + 1) →o Fin (m + 1))
    (i : Fin (b + 1)) :
    dgCoherentBarJoinOrderMap α β (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight a b i) =
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m (β i) := by
  have hi : ¬a + 1 + i.val < a + 1 := by omega
  simp only [dgCoherentBarJoinOrderMap, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom,
    OrderHom.coe_mk, hi,
    dite_false, Nat.add_sub_cancel_left]

lemma dgCoherentBarJoinOrderMap_concat {a b n m r : ℕ}
    (α : Fin (a + 1) →o Fin (n + 1)) (β : Fin (b + 1) →o Fin (m + 1))
    (l : ℕ) (hl : l ≤ r) (f : Fin l →o Fin (a + 1))
    (g : Fin (r - l) →o Fin (b + 1)) (i : Fin r) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat l hl (α.comp f) (β.comp g) i).val =
      (dgCoherentBarJoinOrderMap α β
        (Fin.cast (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat l hl f g i))).val := by
  by_cases hi : i.val < l
  · have he : Fin.cast (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat l hl f g i) =
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft a b (f ⟨i.val, hi⟩) := Fin.ext (by
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat l hl f g i).val = (f ⟨i.val, hi⟩).val
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ hi])
    rw [he, dgCoherentBarJoinOrderMap_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_lt _ _ _ _ _ hi]
    rfl
  · have hge : l ≤ i.val := by omega
    have he : Fin.cast (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat l hl f g i) =
        _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight a b (g ⟨i.val - l, by have := i.isLt; omega⟩) := Fin.ext (by
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat l hl f g i).val = a + 1 + (g ⟨i.val - l, _⟩).val
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ hge])
    rw [he, dgCoherentBarJoinOrderMap_right, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat_of_ge _ _ _ _ _ hge]
    rfl

lemma dgCoherentBarJoinStdSimplex_naturality {a b n m : ℕ}
    (α : ⦋a⦌ ⟶ ⦋n⦌) (β : ⦋b⦌ ⟶ ⦋m⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map α) (SSet.stdSimplex.map β) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso.{u} n m).hom =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso a b).hom ≫ SSet.stdSimplex.map
      (SimplexCategory.mkHom (dgCoherentBarJoinOrderMap α.toOrderHom β.toOrderHom)) := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.concat s.1.val (Nat.le_of_lt_succ s.1.isLt)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv n _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (SSet.stdSimplex.map α) _ s.2.1))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv m _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (SSet.stdSimplex.map β) _ s.2.2)) i).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv_augHom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv_augHom]
  exact dgCoherentBarJoinOrderMap_concat α.toOrderHom β.toOrderHom _ _ _ _ i

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
