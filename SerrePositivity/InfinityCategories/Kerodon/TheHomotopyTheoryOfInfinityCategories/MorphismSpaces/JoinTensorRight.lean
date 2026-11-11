module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensor

/-!
概要：join の右因子と単体集合の直積の比較。
方針：join の切断の右側へ直積の第二成分を制限する。
規約：左因子上では第二成分を忘れる。
使われ方：Kerodon §4.6.2（Tag 01HM） の fat join の比較、§7.1.8。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace Join

/-- 概要：末尾の n-r 個の頂点を全頂点の区間へ含める順序写像。
方針：各値に切断 r を加える。
規約：空区間も許す。
使われ方：Kerodon §4.6.2（Tag 01HM） の右側の単体への制限。 -/
def suffixIncl (n r : ℕ) (_hr : r ≤ n) : Fin (n - r) →o Fin n where
  toFun i := ⟨r + i.val, by have := i.isLt; omega⟩
  monotone' := fun _ _ h ↦ Nat.add_le_add_left h r

/-- 概要：切断の末尾への制限と全体の単体の引き戻しは可換。
方針：右写像の原点移動を打ち消して順序写像の合成を比較する。
規約：添字は頂点数で表す。
使われ方：Kerodon §4.6.2（Tag 01HM） の join と直積の比較射の自然性。 -/
lemma augMap_suffix_rightMap (C : SSet.{u}) {m n : ℕ}
    (α : Fin m →o Fin n) (r : ℕ) (hr : r ≤ n) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj C n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap C (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α r) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap C (suffixIncl n r hr) c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap C (suffixIncl m (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α r) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α r)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap C α c) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_comp]
  congr 1
  ext i
  change r + ((α ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α r + i.val, _⟩).val - r) =
    (α ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α r + i.val, _⟩).val
  have h : r ≤ (α ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α r + i.val, by have := i.isLt; have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le α r; omega⟩).val := by
    apply Nat.le_of_not_lt
    intro h
    have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff α r _).mpr h
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α r + i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α r at hi
    omega
  omega

/-- 概要：直積と join の単体から、右因子だけを直積にした join の単体を作る。
方針：切断を保ち、直積の第二成分を右区間へ制限する。
規約：左因子の単体はそのまま保つ。
使われ方：Kerodon §4.6.2（Tag 01HM） の fat join から join への比較。 -/
def tensorRightSimplex (A B C : SSet.{u}) (n : ℕ)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A B n) (c : C _⦋n⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A (B ⊗ C) n :=
  ⟨s.1, s.2.1, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.augTensorEquiv B C (n + 1 - s.1.val)).symm
    (s.2.2, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap C (suffixIncl (n + 1) s.1.val (Nat.le_of_lt_succ s.1.isLt)) c)⟩

/-- 概要：右因子の直積への比較は単体作用と可換。
方針：右区間への制限の可換性と補った直積の単体作用を使う。
規約：任意の次数を扱う。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較射の自然性。 -/
lemma tensorRightSimplex_naturality (A B C : SSet.{u}) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex A B n) (c : C _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap A (B ⊗ C) α (tensorRightSimplex A B C n s c) =
      tensorRightSimplex A B C m (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap A B α s) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap C α c) := by
  rcases s with ⟨ℓ, a, b⟩
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap, tensorRightSimplex]
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Join.augTensorEquiv_symm_augMap, augMap_suffix_rightMap]
    rfl

end Join

/-- 概要：join と直積を、右因子だけの直積と join へ比較する射。
方針：各次数で切断の右側へ第二成分を制限する。
規約：左因子上では第二成分を忘れる。
使われ方：Kerodon §4.6.2（Tag 01HM）、§7.1.8（Tag 02X8） の join と関手の比較。 -/
def joinTensorRight (A B C : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A B ⊗ C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (B ⊗ C) where
  app n := ↾fun s ↦ Join.tensorRightSimplex A B C n.unop.len s.1 s.2
  naturality {n m} α := by
    obtain ⟨⟨n⟩⟩ := n
    obtain ⟨⟨m⟩⟩ := m
    apply ConcreteCategory.hom_ext
    rintro ⟨s, c⟩
    exact (Join.tensorRightSimplex_naturality A B C α.unop.toOrderHom s c).symm

/-- 概要：右側の直積への比較は右包含と可換。
方針：切断零では末尾への制限が恒等となる。
規約：右因子に直積の両成分を残す。
使われ方：Kerodon §4.6.2（Tag 01HM） の右端点の計算。 -/
lemma joinTensorRight_inr (A B C : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A B ▷ C) ≫ joinTensorRight A B C = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A (B ⊗ C) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨b, c⟩
  change Join.tensorRightSimplex A B C n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr b) c = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr (b, c)
  unfold Join.tensorRightSimplex _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · change (b, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap C (Join.suffixIncl (n + 1) 0 _) c) = (b, c)
    have hp : Join.suffixIncl (n + 1) 0 (Nat.zero_le _) = OrderHom.id := by
      ext i
      simp [Join.suffixIncl]
    rw [hp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_id]

/-- 概要：右側の直積への比較は左包含上で直積の第二成分を忘れる。
方針：右区間が空になる切断を計算する。
規約：左因子はそのまま保つ。
使われ方：Kerodon §4.6.2（Tag 01HM） の左端点の計算。 -/
lemma joinTensorRight_inl (A B C : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A B ▷ C) ≫ joinTensorRight A B C = fst A C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A (B ⊗ C) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, c⟩
  change Join.tensorRightSimplex A B C n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl a) c = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl a
  unfold Join.tensorRightSimplex _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ ?_ ?_ ?_
  · rfl
  · rfl
  · haveI : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (B ⊗ C) (n + 1 - (n + 1))) := by
      rw [Nat.sub_self]
      change Subsingleton PUnit
      infer_instance
    exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
