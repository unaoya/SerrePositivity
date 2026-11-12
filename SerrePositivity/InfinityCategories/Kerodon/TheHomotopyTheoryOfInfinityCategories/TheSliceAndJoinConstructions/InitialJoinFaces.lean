module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialJoinIso

/-!
概要：点と nerve の join の同型は左右の包含を標準の二つの包含に送る。
方針：切断が全頂点数の場合と零の場合の射列を計算する。
規約：点側は新しい始対象、元の nerve 側は WithInitial.incl の nerve。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の相対錐の境界の比較。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C : Type u} [SmallCategory C]

/-- 概要：join の左端の単体は新しい始対象の一定射列になる。
方針：全頂点が切断より前であることと始対象からの射の一意性を使う。
規約：左因子は標準の零単体。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の点側の包含の比較。 -/
lemma initialJoinChain_inl {n : ℕ} (x : (Δ[0] : SSet.{u}) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain (C := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl x) =
      (Functor.const (Fin (n + 1))).obj (WithInitial.star : WithInitial C) := by
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_star _ i i.isLt
  · intro i j f
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_star (C := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl x) i i.isLt
    have : Subsingleton ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain (C := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl x)).obj i ⟶
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain (C := C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inl x)).obj j) := by
      change Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj _ i ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj _ j)
      rw [he]
      infer_instance
    exact Subsingleton.elim _ _

private lemma inr_index {n : ℕ} (F : ComposableArrows C n) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinTailIndex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr (K := (Δ[0] : SSet.{u})) (L := nerve C) F) i
      (Nat.not_lt_zero _) = i := by
  apply Fin.ext
  rfl

private lemma incl_index_heq {n : ℕ} (F : ComposableArrows C n)
    {i j i' j' : Fin (n + 1)} (hi : i = i') (hj : j = j') (f : i ⟶ j) (g : i' ⟶ j') :
    HEq ((WithInitial.incl : C ⥤ WithInitial C).map (F.map f))
      (WithInitial.incl.map (F.map g)) := by
  subst i' j'
  have hf : f = g := Subsingleton.elim _ _
  subst g
  rfl

/-- 概要：join の右端の単体は元の射列を WithInitial へ含めた射列になる。
方針：切断が零なので、後半の添字が元の添字に一致することを使う。
規約：射列の厳密な等式として述べる。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の元の nerve 側の包含の比較。 -/
lemma initialJoinChain_inr {n : ℕ} (F : ComposableArrows C n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinChain (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr (K := (Δ[0] : SSet.{u})) (L := nerve C) F) =
      ((WithInitial.incl : C ⥤ WithInitial C).mapComposableArrows n).obj F := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro i
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr (K := (Δ[0] : SSet.{u})) (L := nerve C) F) i =
      WithInitial.of (F.obj i)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinObj_of _ i (Nat.not_lt_zero _), inr_index]
    rfl
  · intro i j f
    change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr (K := (Δ[0] : SSet.{u})) (L := nerve C) F)
      (leOfHom f)) ((WithInitial.incl : C ⥤ WithInitial C).map (F.map f))
    have hi : ¬ i.val < (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.inr (K := (Δ[0] : SSet.{u})) (L := nerve C) F).1.val :=
      Nat.not_lt_zero _
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinMap, dite_eq_right hi, eqToHom_comp_heq_iff,
      comp_eqToHom_heq_iff]
    exact incl_index_heq F (inr_index F i) (inr_index F j) _ f

/-- 概要：join の同型の点側の包含は新しい始対象の頂点である。
方針：全次数で一定射列への一致を使う。
規約：点の頂点は nervePoint で表示する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の相対錐の先端の可換図式。 -/
@[reassoc]
lemma joinInl_initialJoinNerveMap (C : Type u) [SmallCategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) (nerve C) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveMap C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (WithInitial.star : WithInitial C) := by
  ext n x
  exact initialJoinChain_inl x

/-- 概要：join の同型の元の nerve 側の包含は WithInitial.incl の nerve である。
方針：全次数で元の射列の包含への一致を使う。
規約：元の圏の非空性は要求しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V） の相対錐の底面の可換図式。 -/
@[reassoc]
lemma joinInr_initialJoinNerveMap (C : Type u) [SmallCategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) (nerve C) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialJoinNerveMap C =
      nerveMap (WithInitial.incl : C ⥤ WithInitial C) := by
  ext n F
  exact initialJoinChain_inr F

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
