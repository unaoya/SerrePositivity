module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.InitialNerveOldPart

/-!
概要：WithInitial の nerve の単体から join 型の切断と後半の単体を構成する。
方針：切断以後の区間を元の圏へ戻し、後半が空の場合は補った空単体を使う。
規約：次数ごとのデータを構成する段階であり、単体的自然性と比較射の逆関係は後続。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と点の join の同定。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
variable {C : Type u} [SmallCategory C]

/-- 概要：切断以後の区間を元の射列の頂点の区間へ含める単調写像。
方針：添字に新しい始対象の頂点数を加える。
規約：後半が非空である切断の条件を明示する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
def initialNerveTailIndex {n : ℕ} (F : ComposableArrows (WithInitial C) n)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F ≤ n) : Fin (n - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F + 1) →o Fin (n + 1) where
  toFun i := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F + i.val, by have := i.isLt; omega⟩
  monotone' _ _ h := Nat.add_le_add_left h _
/-- 概要：切断以後の区間の全頂点は新しい始対象でない。
方針：新しい始対象なら切断より前であるという特徴づけと添字の下界を使う。
規約：元の圏の非空性は別途仮定しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveTail_nonstar {n : ℕ} (F : ComposableArrows (WithInitial C) n)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F ≤ n) (i : Fin (n - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F + 1)) :
    F.obj (initialNerveTailIndex F h i) ≠ WithInitial.star := by
  intro hs
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerve_lt_cut_iff F (initialNerveTailIndex F h i)).2 hs
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F + i.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F at hi
  omega
/-- 概要：切断以後の非空の射列を元の圏の射列として復元する。
方針：区間の包含で制限して新しい始対象でない部分を元の圏へ戻す。
規約：長さは n から切断の頂点数を引いた値。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
def initialNerveTail {n : ℕ} (F : ComposableArrows (WithInitial C) n)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F ≤ n) : ComposableArrows C (n - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveOldFunctor ((initialNerveTailIndex F h).monotone.functor ⋙ F)
    (initialNerveTail_nonstar F h)
/-- 概要：復元した後半の頂点の包含は元の射列の対応する頂点に等しい。
方針：元の圏への復元の対象の等式を区間の制限に適用する。
規約：等式の移送が必要な端点を明示する。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveTail_obj {n : ℕ} (F : ComposableArrows (WithInitial C) n)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F ≤ n) (i : Fin (n - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F + 1)) :
    WithInitial.of ((initialNerveTail F h).obj i) =
      F.obj (initialNerveTailIndex F h i) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveOldFunctor_obj _ _ _
/-- 概要：復元した後半の射の包含は元の射列の射と端点の移送を介して一致する。
方針：復元した関手の射の移送の式を区間の各射に適用する。
規約：端点の等式は initialNerveTail_obj の等式を使う。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveTail_map {n : ℕ} (F : ComposableArrows (WithInitial C) n)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F ≤ n) {i j : Fin (n - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F + 1)} (f : i ⟶ j) :
    eqToHom (initialNerveTail_obj F h i) ≫
        F.map ((initialNerveTailIndex F h).monotone.functor.map f) =
      (WithInitial.incl : C ⥤ WithInitial C).map ((initialNerveTail F h).map f) ≫
        eqToHom (initialNerveTail_obj F h j) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveOldFunctor_map _ _ _
/-- 概要：WithInitial の nerve の単体から点と元の nerve の join 型の単体を構成する。
方針：左は切断の頂点数の一定単体、右は非空なら復元した後半、空なら補った空単体にする。
規約：この定義だけでは単体的自然性や比較の逆関係を主張しない。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
noncomputable def initialNerveJoinSimplex {n : ℕ} (F : ComposableArrows (WithInitial C) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[0] : SSet.{u}) (nerve C) n := by
  refine ⟨⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F, by have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut_le F; omega⟩, ?_, ?_⟩
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 0 _).symm (OrderHom.const _ 0)
  · change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (nerve C) (n + 1 - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F)
    by_cases h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F ≤ n
    · rw [Nat.succ_sub h]
      exact initialNerveTail F h
    · have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F = n + 1 := by have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut_le F; omega
      rw [hc, Nat.sub_self]
      exact PUnit.unit
/-- 概要：構成した join 型の単体の切断は元の射列の切断である。
方針：直和の添字の定義を読む。
規約：後半が空の場合と非空の場合の両方を含む。
使われ方：HTT 1.2.8、Kerodon 4.3.5（Tag 017V）、7.5.3.12（Tag 03B1） の nerve と join の比較。 -/
lemma initialNerveJoinSimplex_cut {n : ℕ} (F : ComposableArrows (WithInitial C) n) :
    (initialNerveJoinSimplex F).1.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.initialNerveCut F := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
