module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCyclePostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorGradedCycleLifting
/-!
概要：指定余単位の実閉 cycle から、元の全 Hom に作用する鎖写像を構成する。
方針：実 dg 関手と閉後合成を合成し、斉次前合成との交換を証明する。
規約：全整数次数を保持する。使われ方：一般 RHom の写像空間普遍性の検査。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) (E : Type w)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
variable (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C E) {t : C} {y : E}
  (ε : _root_.SerrePositivity.DifferentialGraded.zeroCycles (_root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj t) y))
/-- 元の dg 関手に続く、同じ余単位による全 Hom 鎖写像。 -/
def dgCounitColumn (x : C) : _root_.SerrePositivity.DifferentialGraded.homObject R C x t ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E (G.obj x) y :=
  G.map x t ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCyclePostcomposition R E (G.obj x) ε
/-- 余単位の全整数次数での作用は元の斉次合成。 -/
lemma dgCounitColumn_f (x : C) (n : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R x t n) :
    (dgCounitColumn R C E G ε x).f n a =
      _root_.SerrePositivity.DifferentialGraded.compose R ε.val ((G.map x t).f n a) (add_zero n) := rfl
/-- 同じ余単位による鎖写像は斉次前合成と厳密に可換。 -/
lemma dgCounitColumn_compose {x z : C} {p q k : ℤ}
    (a : _root_.SerrePositivity.DifferentialGraded.GradedHom R z t q) (b : _root_.SerrePositivity.DifferentialGraded.GradedHom R x z p) (hpq : p + q = k) :
    (dgCounitColumn R C E G ε x).f k (_root_.SerrePositivity.DifferentialGraded.compose R a b hpq) =
      _root_.SerrePositivity.DifferentialGraded.compose R ((dgCounitColumn R C E G ε z).f q a) ((G.map x z).f p b) hpq := by
  rw [dgCounitColumn_f, dgCounitColumn_f, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveGradedCompose_assoc R E ((G.map x z).f p b) ((G.map z t).f q a) ε.val
    hpq (add_zero q) (add_zero k) hpq
end SerrePositivity.InfinityCategories.Project.DerivedCategories
