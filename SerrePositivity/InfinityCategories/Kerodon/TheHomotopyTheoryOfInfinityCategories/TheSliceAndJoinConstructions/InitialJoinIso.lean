module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinRetraction

/-!
概要：点と nerve の join と、新しい始対象を付加した圏の nerve の同型。
方針：切断と後半の全対象・全射から join の単体を一意に復元する。
規約：任意の小さい圏を扱い、空の圏にも適用する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の相対錐と WithInitial の標準境界の同定。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C : Type u} [SmallCategory C]

private lemma aug_ext {r : ℕ} (τ τ' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r)
    (ho : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj τ i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj τ' i)
    (hm : ∀ (i j : Fin r) (h : i ≤ j), HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap τ h) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap τ' h)) :
    τ = τ' := by
  cases r with
  | zero => exact @Subsingleton.elim PUnit inferInstance _ _
  | succ r =>
    refine CategoryTheory.Functor.hext ho ?_
    intro i j f
    exact hm i j (leOfHom f)

private def oldIndex {n : ℕ} (ℓ : Fin (n + 2)) (i : Fin (n + 1 - ℓ.val)) :
    Fin (n + 1) := ⟨ℓ.val + i.val, by have := i.isLt; omega⟩

private lemma oldIndex_not_lt {n : ℕ} (ℓ : Fin (n + 2))
    (i : Fin (n + 1 - ℓ.val)) : ¬ (oldIndex ℓ i).val < ℓ.val := by
  change ¬ ℓ.val + i.val < ℓ.val
  omega

private lemma tailIndex_oldIndex {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) (i : Fin (n + 1 - s.1.val)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinTailIndex s (oldIndex s.1 i) (oldIndex_not_lt s.1 i) = i := by
  apply Fin.ext
  change s.1.val + i.val - s.1.val = i.val
  omega

private lemma old_obj {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n)
    (i : Fin (n + 1 - s.1.val)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain s).obj (oldIndex s.1 i) = WithInitial.of (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj s.2.2 i) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj s _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_of _ _ (oldIndex_not_lt s.1 i), tailIndex_oldIndex]

private lemma incl_heq {a b c d : C} (ha : a = c) (hb : b = d)
    (f : a ⟶ b) (g : c ⟶ d)
    (hf : HEq ((WithInitial.incl : C ⥤ WithInitial C).map f) (WithInitial.incl.map g)) :
    HEq f g := by
  subst c d
  exact hf

private lemma aug_incl_index_heq {r : ℕ} (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) r)
    {i j i' j' : Fin r} (hi : i = i') (hj : j = j') (h : i ≤ j) (h' : i' ≤ j') :
    HEq ((WithInitial.incl : C ⥤ WithInitial C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap τ h))
      (WithInitial.incl.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap τ h')) := by
  subst i' j'
  rfl

private lemma old_map {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n)
    (i j : Fin (n + 1 - s.1.val)) (h : i ≤ j) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain s).map (homOfLE (show oldIndex s.1 i ≤ oldIndex s.1 j from
      Nat.add_le_add_left h _)))
      ((WithInitial.incl : C ⥤ WithInitial C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveMap s.2.2 h)) := by
  change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinMap s (Nat.add_le_add_left h s.1.val)) _
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinMap, dite_eq_right (oldIndex_not_lt s.1 i),
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  exact aug_incl_index_heq s.2.2 (tailIndex_oldIndex s i) (tailIndex_oldIndex s j) _ h

/-- 概要：join の単体から WithInitial の射列への比較は各次数で単射である。
方針：射列から切断を読み戻し、後半の全対象・全射と一点の前半の一意性で比較する。
規約：元の圏に対象がなくても同じ証明を使う。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較射の同型性。 -/
lemma initialJoinChain_injective (n : ℕ) :
    Function.Injective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain (C := C) (n := n)) := by
  intro s t hst
  have hc : s.1 = t.1 := Fin.ext (by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut_initialJoinChain s, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut_initialJoinChain t, hst])
  rcases s with ⟨ℓ, x, y⟩
  rcases t with ⟨ℓ', x', y'⟩
  dsimp only at hc
  subst ℓ'
  have hx : x = x' := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 0 ℓ.val).injective
    apply OrderHom.ext
    funext i
    apply Fin.ext
    have h₁ := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 0 ℓ.val) x i).isLt
    have h₂ := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 0 ℓ.val) x' i).isLt
    omega
  have ho : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj y i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.augNerveObj y' i := by
    intro i
    apply WithInitial.of.inj
    exact (old_obj ⟨ℓ, x, y⟩ i).symm.trans
      ((congrArg (fun F => F.obj (oldIndex ℓ i)) hst).trans (old_obj ⟨ℓ, x', y'⟩ i))
  have hy : y = y' := by
    refine aug_ext y y' ho ?_
    intro i j hij
    apply incl_heq (ho i) (ho j)
    refine (old_map ⟨ℓ, x, y⟩ i j hij).symm.trans ?_
    have hh := CategoryTheory.Functor.hcongr_hom hst (homOfLE
      (show oldIndex ℓ i ≤ oldIndex ℓ j from Nat.add_le_add_left hij _))
    exact hh.trans (old_map ⟨ℓ, x', y'⟩ i j hij)
  cases hx
  cases hy
  rfl

/-- 概要：join の単体を射列へ写して再び分解すると元の単体になる。
方針：射列へ戻す構成の単射性と、射列側の逆関係を使う。
規約：切断だけでなく前半・後半の全データの厳密な等式。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較射の逆写像。 -/
lemma initialNerveJoinSimplex_initialJoinChain {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain s) = s := by
  apply initialJoinChain_injective n
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain_initialNerveJoinSimplex _

/-- 概要：射列の join 型への分解は全ての単体作用素と可換である。
方針：逆向きの構成の単射性と自然性で分解後の二つの単体を比較する。
規約：面と退化を含む全ての単体作用素について厳密に可換。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の比較の逆射の自然性。 -/
lemma initialNerveJoinSimplex_naturality {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (F : ComposableArrows (WithInitial C) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex ((nerve (WithInitial C)).map α.op F) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap Δ[0] (nerve C) α.toOrderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex F) := by
  apply initialJoinChain_injective m
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain_initialNerveJoinSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain_simplexMap,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain_initialNerveJoinSimplex]

/-- 概要：WithInitial の nerve の単体を切断と後半で分解する単体的射。
方針：次数ごとの分解とその単体的自然性を組み合わせる。
規約：新しい始対象以外の対象から元の圏の対象を復元する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の点と nerve の join の同型の逆射。 -/
noncomputable def initialNerveJoinMap (C : Type u) [SmallCategory C] :
    nerve (WithInitial C) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (nerve C) where
  app n := ↾(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveJoinSimplex (C := C))
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro F
    exact initialNerveJoinSimplex_naturality f.unop F

/-- 概要：点と圏の nerve の join は、新しい始対象を付加した圏の nerve と同型である。
方針：切断と後半による分解と射列への復元を、両向きの厳密な逆関係で組み合わせる。
規約：任意の小さい圏を扱い、対象の非空性を要求しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の相対錐と標準境界の同定。 -/
noncomputable def initialJoinNerveIso (C : Type u) [SmallCategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) (nerve C) ≅ nerve (WithInitial C) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveMap C
  inv := initialNerveJoinMap C
  hom_inv_id := by
    ext n s
    exact initialNerveJoinSimplex_initialJoinChain s
  inv_hom_id := by
    ext n F
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain_initialNerveJoinSimplex F

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
