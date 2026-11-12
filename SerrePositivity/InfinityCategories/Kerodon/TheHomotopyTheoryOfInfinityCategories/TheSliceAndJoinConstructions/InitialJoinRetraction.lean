module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinNaturality

/-!
概要：WithInitial の射列を join 型へ分解してから戻す比較の逆関係。
方針：切断より前は始対象、後は復元した射列の対象と射で比較する。
規約：空の後半も含め、元の圏の非空性は仮定しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の点と nerve の join の同型。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C : Type u} [SmallCategory C]

/-- 概要：分解した単体の非空の後半は、復元した元の射列と異種等式で一致する。
方針：後半の定義を展開し、頂点数の等式による移送を取り除く。
規約：後半が非空となる切断の上界を明示する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較の逆関係の対象と射の評価。 -/
lemma initialNerveJoinSimplex_right_heq {n : ℕ}
    (F : ComposableArrows (WithInitial C) n) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F ≤ n) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex F).2.2 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveTail F h) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex]
  rw [dite_eq_left h]
  exact cast_heq _ _

private lemma aug_obj_heq {r r' : ℕ} (hr : r = r')
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r) (τ' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r') (hτ : HEq τ τ')
    (i : Fin r) (i' : Fin r') (hi : i.val = i'.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj τ i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj τ' i' := by
  subst r'
  have ht := eq_of_heq hτ
  have he : i = i' := Fin.ext hi
  subst τ' i'
  rfl

/-- 概要：射列を join 型へ分解して戻した各頂点は元の頂点に等しい。
方針：前半は切断の特徴づけ、後半は添字の移送と復元した射列の対象の式を使う。
規約：元の圏の対象を選ぶ操作を含まない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の nerve と点の join の比較の逆関係。 -/
lemma initialJoinObj_initialNerveJoinSimplex {n : ℕ}
    (F : ComposableArrows (WithInitial C) n) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex F) i = F.obj i := by
  by_cases hi : i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_star _ i hi).trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerve_lt_cut_iff F i).1 hi).symm
  · have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F ≤ n := by have := i.isLt; omega
    let j : Fin (n - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F + 1) :=
      ⟨i.val - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F, by have := i.isLt; omega⟩
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_of _ i hi]
    have he := aug_obj_heq (Nat.succ_sub h) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex F).2.2
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveTail F h) (initialNerveJoinSimplex_right_heq F h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinTailIndex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex F) i hi) j rfl
    rw [he]
    change WithInitial.of ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveTail F h).obj j) = F.obj i
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveTail_obj]
    congr 1
    apply Fin.ext
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F + (i.val - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F) = i.val
    omega

private lemma aug_incl_map_heq {r r' : ℕ} (hr : r = r')
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r) (τ' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r') (hτ : HEq τ τ')
    (i j : Fin r) (i' j' : Fin r') (hi : i.val = i'.val) (hj : j.val = j'.val)
    (h : i ≤ j) (h' : i' ≤ j') :
    HEq ((WithInitial.incl : C ⥤ WithInitial C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap τ h))
      (WithInitial.incl.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap τ' h')) := by
  subst r'
  have ht := eq_of_heq hτ
  have hei : i = i' := Fin.ext hi
  have hej : j = j' := Fin.ext hj
  subst τ' i' j'
  rfl

private lemma functor_map_heq {J : Type v} [Category.{w} J] (G : J ⥤ WithInitial C)
    {a b c d : J} (ha : a = c) (hb : b = d) (f : a ⟶ b) (g : c ⟶ d)
    (hf : HEq f g) : HEq (G.map f) (G.map g) := by
  subst c d
  exact heq_of_eq (congrArg G.map (eq_of_heq hf))

/-- 概要：射列を join 型へ分解して戻した各射は元の射に端点の移送を介して一致する。
方針：前半からの射は始対象の一意性、後半の射は復元した射列の射の式を使う。
規約：対象の等式で型が異なる射を HEq で比較する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の nerve と点の join の比較の逆関係。 -/
lemma initialJoinMap_initialNerveJoinSimplex {n : ℕ}
    (F : ComposableArrows (WithInitial C) n) {i j : Fin (n + 1)} (hij : i ≤ j) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex F) hij) (F.map (homOfLE hij)) := by
  by_cases hi : i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F
  · apply (conj_eqToHom_iff_heq _ _
      (initialJoinObj_initialNerveJoinSimplex F i)
      (initialJoinObj_initialNerveJoinSimplex F j)).1
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_star (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex F) i hi
    have : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex F) i ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex F) j) := by
      rw [he]
      infer_instance
    exact Subsingleton.elim _ _
  · have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F ≤ n := by have := i.isLt; omega
    have hj : ¬ j.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F := fun hh => hi (lt_of_le_of_lt hij hh)
    let i' : Fin (n - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F + 1) :=
      ⟨i.val - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F, by have := i.isLt; omega⟩
    let j' : Fin (n - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F + 1) :=
      ⟨j.val - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F, by have := j.isLt; omega⟩
    have hij' : i' ≤ j' := Nat.sub_le_sub_right hij _
    have hi' : ¬ i.val < (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex F).1.val := hi
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinMap, dite_eq_right hi', eqToHom_comp_heq_iff,
      comp_eqToHom_heq_iff]
    refine (aug_incl_map_heq (Nat.succ_sub h) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex F).2.2
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveTail F h) (initialNerveJoinSimplex_right_heq F h)
      _ _ i' j' rfl rfl _ hij').trans ?_
    change HEq (WithInitial.incl.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveTail F h).map (homOfLE hij')))
      (F.map (homOfLE hij))
    have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveTail_map F h (homOfLE hij')
    have ht : HEq (WithInitial.incl.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveTail F h).map (homOfLE hij')))
        (F.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveTailIndex F h).monotone.functor.map (homOfLE hij'))) := by
      have he := heq_of_eq hm
      simp only [eqToHom_comp_heq_iff, heq_comp_eqToHom_iff] at he
      exact he.symm
    refine ht.trans ?_
    have hei : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveTailIndex F h i' = i := Fin.ext (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F + (i.val - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F) = i.val
      omega)
    have hej : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveTailIndex F h j' = j := Fin.ext (by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F + (j.val - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F) = j.val
      omega)
    have hf : HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveTailIndex F h).monotone.functor.map (homOfLE hij'))
        (homOfLE hij) := by
      apply (conj_eqToHom_iff_heq _ _ hei hej).1
      exact Subsingleton.elim _ _
    exact functor_map_heq F hei hej _ _ hf

/-- 概要：WithInitial の射列を join 型へ分解して戻すと元の射列になる。
方針：復元した対象と射の一致を関手の外延性に適用する。
規約：任意の長さの射列と空の後半を含む厳密な等式。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較射の全射性。 -/
lemma initialJoinChain_initialNerveJoinSimplex {n : ℕ}
    (F : ComposableArrows (WithInitial C) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex F) = F := by
  refine CategoryTheory.Functor.hext (initialJoinObj_initialNerveJoinSimplex F) ?_
  intro i j f
  exact initialJoinMap_initialNerveJoinSimplex F (leOfHom f)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
