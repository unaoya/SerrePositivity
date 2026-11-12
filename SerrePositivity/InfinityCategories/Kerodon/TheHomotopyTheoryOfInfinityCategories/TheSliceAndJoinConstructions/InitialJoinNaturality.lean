module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinChain

/-!
概要：join 型の単体から WithInitial の射列への構成の単体的自然性。
方針：切断の逆像と右側の原点移動を比較し、対象と射の再添字付けを検証する。
規約：面と退化を含む全ての順序写像を扱う。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の点と nerve の join の比較射。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C : Type u} [SmallCategory C]

/-- 概要：切断の引き戻し後の後半の添字は、右制限の順序写像で元の後半へ写る。
方針：切断を足して引く式を頂点の下界で簡約する。
規約：切断以後の頂点だけを評価する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の join の単体作用との可換性。 -/
lemma initialJoinTailIndex_simplexMap {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1))
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) (i : Fin (m + 1))
    (hi : ¬ i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α s.1.val
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinTailIndex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap Δ[0] (nerve C) α s) i hi) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinTailIndex s (α i) (fun h => hi ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff α s.1.val i).2 h)) := by
  apply Fin.ext
  change (α ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val + (i.val - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val), _⟩).val -
      s.1.val = (α i).val - s.1.val
  have he : (⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val + (i.val - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val),
      by have := i.isLt; omega⟩ : Fin (m + 1)) = i := Fin.ext (by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val + (i.val - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val) = i.val
        omega)
  rw [he]

/-- 概要：join から読んだ頂点は順序写像による引き戻しと可換である。
方針：切断の前後で場合分けし、後半は補った nerve の評価の自然性を使う。
規約：切断の前半は新しい始対象に一致する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較射の対象の自然性。 -/
lemma initialJoinObj_simplexMap {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1))
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) (i : Fin (m + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap Δ[0] (nerve C) α s) i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj s (α i) := by
  by_cases hi : i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val
  · have ha := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff α s.1.val i).1 hi
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_star _ i hi).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_star s (α i) ha).symm
  · have ha : ¬ (α i).val < s.1.val :=
      fun h => hi ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff α s.1.val i).2 h)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_of _ i hi, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_of s (α i) ha]
    congr 1
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap (nerve C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α s.1.val) s.2.2) _ = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj_augMap, initialJoinTailIndex_simplexMap]

private lemma incl_map_heq {a b c d : C} (ha : a = c) (hb : b = d)
    (f : a ⟶ b) (g : c ⟶ d) (hf : HEq f g) :
    HEq ((WithInitial.incl : C ⥤ WithInitial C).map f) (WithInitial.incl.map g) := by
  subst c d
  exact heq_of_eq (congrArg (WithInitial.incl : C ⥤ WithInitial C).map (eq_of_heq hf))

private lemma aug_map_heq {m r : ℕ} (α : Fin m →o Fin r)
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r) {i j : Fin m} (h : i ≤ j) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap (nerve C) α τ) h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap τ (α.monotone h)) := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    cases r with
    | zero => exact Fin.elim0 (α i)
    | succ r => rfl

private lemma aug_map_index_heq {r : ℕ} (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r)
    {i j i' j' : Fin r} (hi : i = i') (hj : j = j') (h : i ≤ j) (h' : i' ≤ j') :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap τ h') := by
  subst i' j'
  rfl

/-- 概要：join から読んだ射は順序写像による引き戻しと端点の移送を介して一致する。
方針：始点が前半なら始対象の一意性、後半なら nerve の再添字付けと添字の一致を使う。
規約：異なる端点の型を HEq で明示し、面と退化を同時に扱う。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較射の射の自然性。 -/
lemma initialJoinMap_simplexMap {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1))
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n)
    {i j : Fin (m + 1)} (h : i ≤ j) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap Δ[0] (nerve C) α s) h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinMap s (α.monotone h)) := by
  by_cases hi : i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val
  · apply (conj_eqToHom_iff_heq _ _
      (initialJoinObj_simplexMap α s i) (initialJoinObj_simplexMap α s j)).1
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_star (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap Δ[0] (nerve C) α s) i hi
    have : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap Δ[0] (nerve C) α s) i ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap Δ[0] (nerve C) α s) j) := by
      rw [he]
      infer_instance
    exact Subsingleton.elim _ _
  · have ha : ¬ (α i).val < s.1.val :=
      fun hh => hi ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff α s.1.val i).2 hh)
    have hj : ¬ j.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val := fun hh => hi (lt_of_le_of_lt h hh)
    have hi' : ¬ i.val < (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap Δ[0] (nerve C) α s).1.val := hi
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinMap, dite_eq_right hi', dite_eq_right ha,
      eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    apply incl_map_heq
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj_augMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α s.1.val) s.2.2 _).trans
        (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj s.2.2) (initialJoinTailIndex_simplexMap α s i hi))
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj_augMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α s.1.val) s.2.2 _).trans
        (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj s.2.2) (initialJoinTailIndex_simplexMap α s j hj))
    · exact (aug_map_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α s.1.val) s.2.2 _).trans
        (aug_map_index_heq s.2.2 (initialJoinTailIndex_simplexMap α s i hi)
          (initialJoinTailIndex_simplexMap α s j hj) _ _)

/-- 概要：join の単体から構成した射列は全ての単体作用素と可換である。
方針：対象の等式と射の異種等式を関手の外延性に適用する。
規約：等式は射列の厳密な等式であり、同型だけではない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の単体集合の比較射の自然性。 -/
lemma initialJoinChain_simplexMap {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap Δ[0] (nerve C) α.toOrderHom s) =
      (nerve (WithInitial C)).map α.op (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain s) := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · exact initialJoinObj_simplexMap α.toOrderHom s
  · intro i j f
    exact initialJoinMap_simplexMap α.toOrderHom s (leOfHom f)

/-- 概要：点と通常の nerve の join から WithInitial の nerve への単体的比較射。
方針：各次数で構成した射列と、全ての単体作用素との可換性を組み合わせる。
規約：この段階では比較射の同型性は主張しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の相対錐の標準境界との同定。 -/
def initialJoinNerveMap (C : Type u) [SmallCategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (nerve C) ⟶ nerve (WithInitial C) where
  app n := ↾(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain (C := C))
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro s
    exact initialJoinChain_simplexMap f.unop s

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
