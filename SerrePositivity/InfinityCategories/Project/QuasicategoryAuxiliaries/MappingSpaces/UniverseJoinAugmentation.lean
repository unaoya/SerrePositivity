module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join

/-! # 空単体を補った単体の宇宙移送

概要：join の空区間を含む二因子を ULift と比較する。
方針：頂点数零では一点の一意性、正の頂点数では ULift の上げ下げを使う。
規約：切断と順序写像を変更しない。使われ方：join と slice/coslice の宇宙比較。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 空単体を補った単体を上の宇宙へ送る。 -/
def uliftJoinAugUp (K : SSet.{u}) : (r : ℕ) → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K r →
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj ((SSet.uliftFunctor.{v, u}).obj K) r
  | 0, _ => PUnit.unit
  | _ + 1, x => ULift.up x

/-- 空単体を補った単体を元の宇宙へ戻す。 -/
def uliftJoinAugDown (K : SSet.{u}) : (r : ℕ) →
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj ((SSet.uliftFunctor.{v, u}).obj K) r → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K r
  | 0, _ => PUnit.unit
  | _ + 1, x => x.down

/-- 空区間を含め、上げ下げの合成は恒等。 -/
lemma uliftJoinAug_down_up (K : SSet.{u}) (r : ℕ) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K r) :
    uliftJoinAugDown K r (uliftJoinAugUp.{u, v} K r x) = x := by
  cases r with
  | zero => exact @Subsingleton.elim PUnit inferInstance _ _
  | succ r => rfl

/-- 空区間を含め、下げ上げの合成も恒等。 -/
lemma uliftJoinAug_up_down (K : SSet.{u}) (r : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj ((SSet.uliftFunctor.{v, u}).obj K) r) :
    uliftJoinAugUp K r (uliftJoinAugDown K r x) = x := by
  cases r with
  | zero => exact @Subsingleton.elim PUnit inferInstance _ _
  | succ r => rfl

/-- 空区間を含む上げ操作は単調写像による引き戻しと可換。 -/
lemma uliftJoinAugUp_map (K : SSet.{u}) {m n : ℕ} (α : Fin m →o Fin n)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K n) :
    uliftJoinAugUp.{u, v} K m (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K α x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap ((SSet.uliftFunctor.{v, u}).obj K) α (uliftJoinAugUp K n x) := by
  cases m with
  | zero => rfl
  | succ m =>
    cases n with
    | zero => exact Fin.elim0 (α 0)
    | succ n => rfl

/-- 空区間を含む下げ操作は単調写像による引き戻しと可換。 -/
lemma uliftJoinAugDown_map (K : SSet.{u}) {m n : ℕ} (α : Fin m →o Fin n)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj ((SSet.uliftFunctor.{v, u}).obj K) n) :
    uliftJoinAugDown K m (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap ((SSet.uliftFunctor.{v, u}).obj K) α x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap K α (uliftJoinAugDown K n x) := by
  cases m with
  | zero => rfl
  | succ m =>
    cases n with
    | zero => exact Fin.elim0 (α 0)
    | succ n => rfl

/-- 空単体を含む上げ操作は単体集合の射による像と可換。 -/
lemma uliftJoinAugUp_hom {K L : SSet.{u}} (f : K ⟶ L) (r : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K r) :
    uliftJoinAugUp.{u, v} L r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f r x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom ((SSet.uliftFunctor.{v, u}).map f) r (uliftJoinAugUp K r x) := by
  cases r <;> rfl

/-- 空単体を含む下げ操作は単体集合の射による像と可換。 -/
lemma uliftJoinAugDown_hom {K L : SSet.{u}} (f : K ⟶ L) (r : ℕ)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj ((SSet.uliftFunctor.{v, u}).obj K) r) :
    uliftJoinAugDown L r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom ((SSet.uliftFunctor.{v, u}).map f) r x) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom f r (uliftJoinAugDown K r x) := by
  cases r <;> rfl

/-- 空区間の上げた成分は上の宇宙の唯一の空成分に等しい。 -/
lemma uliftJoinAugUp_eq_of_zero (K : SSet.{u}) (r : ℕ) (hr : r = 0)
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj K r) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj ((SSet.uliftFunctor.{v, u}).obj K) r) :
    uliftJoinAugUp K r x = y := by
  subst r
  exact @Subsingleton.elim PUnit inferInstance _ _

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
