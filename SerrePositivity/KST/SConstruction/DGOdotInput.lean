module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGAlgebraExtensionInfinity
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraInvariantComposition

/-! # 元の非可換 dg 代数四角形の実入力
概要：複体のモノイド対象と元の四代数射・可換式を保持する。
方針：D の dgAlgebraMap と Sp の既存合成式を読み取り専用で使う。
規約：可換代数性・平坦性は要求しない。使われ方：dg 増強流の具体的 ⊙ 入力。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories

/-- 元の四代数・四射と厳密可換式を保持する、具体的 dg ⊙ の入力。 -/
structure DGOdotInput (R : Type u) [CommRing R] where
  source : Mon (Complex R)
  left : Mon (Complex R)
  right : Mon (Complex R)
  corner : Mon (Complex R)
  top : source ⟶ left
  side : source ⟶ right
  lower : left ⟶ corner
  upper : right ⟶ corner
  commutes : top ≫ lower = side ≫ upper

variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 元の代数四角形の可換式を、同じ四つの厳密 dg 関手の可換式へ移す。 -/
lemma dgOdotInput_dg_commutes :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper) := by
  calc
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (d.top ≫ d.lower) :=
      LocalizingInvariants.DGAlgebra.dgAlgebraMap_comp R d.top d.lower
    _ = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (d.side ≫ d.upper) :=
      congrArg (fun f : d.source ⟶ d.corner => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R f) d.commutes
    _ = _ := (LocalizingInvariants.DGAlgebra.dgAlgebraMap_comp R d.side d.upper).symm

/-- 元の右代数の一対象 dg 圏の、同じ指定対象。 -/
def dgOdotInputRightPoint : _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.right := Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star

/-- 元の始域代数の一対象 dg 圏の、同じ指定対象。 -/
def dgOdotInputSourcePoint : _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R d.source := Opposite.op _root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.DGAlgebraPoint.star

end SerrePositivity.KST.SConstruction
