module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorBaseChange

/-!
概要：任意の pullback 表示の相対関手空間を、元の標的への相対関手空間へ移す。
方針：元の射への後合成と pullback への持ち上げを、全パラメーターで curry する。
規約：合成した底の図式は指定した厳密な等式で固定する。
使われ方：底変換した両射影間の Hom と、元の標的へ写す局所 Hom の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

variable {X P E A B : SSet.{u}} {i : P ⟶ E} {r : P ⟶ A} {p : E ⟶ B} {f : A ⟶ B}
  (hs : IsPullback i r p f) (a : X ⟶ A) (b : X ⟶ B) (hab : a ≫ f = b)

/-- pullback の全空間への相対関手を、元の標的への同じ相対関手へ写す。 -/
def relativeFunctorIsPullbackForward : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p b :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (𝟙 _) ≫ i) (by
    rw [Category.assoc, hs.w, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection,
      Category.assoc, hab])

/-- 元の標的への相対関手を、指定した同じ pullback の全空間へ戻す。 -/
def relativeFunctorIsPullbackBackward : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p b ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorCurry
    (hs.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (𝟙 _)) (fst X _ ≫ a) (by
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection, Category.assoc, hab]))
    (hs.lift_snd _ _ _)

/-- 順方向の全パラメーターの展開は、元の標的への後合成そのもの。 -/
lemma relativeFunctorIsPullbackForward_uncurry {T : SSet.{u}}
    (k : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (k ≫ relativeFunctorIsPullbackForward hs a b hab) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry k ≫ i := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorUncurry_naturality, relativeFunctorIsPullbackForward,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry, ← Category.assoc]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorUncurry_naturality (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace r a)) k
  rw [Category.comp_id] at h
  rw [← h]

/-- 逆方向の全パラメーターの展開は、元の二つの射の pullback への持ち上げ。 -/
lemma relativeFunctorIsPullbackBackward_uncurry {T : SSet.{u}}
    (k : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry (k ≫ relativeFunctorIsPullbackBackward hs a b hab) =
      hs.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry k) (fst X T ≫ a) (by
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_projection, Category.assoc, hab]) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorUncurry_naturality, relativeFunctorIsPullbackBackward,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_curry]
  apply hs.hom_ext
  · rw [Category.assoc, hs.lift_fst, hs.lift_fst]
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorUncurry_naturality (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace p b)) k
    simpa only [Category.comp_id] using h.symm
  · rw [Category.assoc, hs.lift_snd, hs.lift_snd, ← Category.assoc, whiskerLeft_fst]

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
