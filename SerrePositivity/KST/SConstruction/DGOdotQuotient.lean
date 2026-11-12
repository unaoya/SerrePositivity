module
public import SerrePositivity.KST.SConstruction.DGOdotInput
public import SerrePositivity.KST.SConstruction.DGSmallPerfectSquareRightEnd

/-! # 実 dg 代数四角形の元の Perf 比較対角商
概要：元の四代数射から、実延長像を保持する小模型・比較対角・指定商 End を構成する。
方針：元の dgAlgebraMap と可換式を、検証済みの共通小模型構成へ渡す。
規約：生成性・lax pullback 同定は未主張。使われ方：具体的 ⊙ の代数化。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.left d)
local notation "D" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)

/-- 元の実代数四角形から構成した、同じ実 Perf 比較対角の指定商 End 入力。 -/
def dgOdotQuotientInput :=
  dgSmallPerfectSquareQuotientInput R (A) (C) (D) (E) (L) (G) (p) (q)
    (dgOdotInput_dg_commutes R d) (dgOdotInputRightPoint R d)

/-- 同じ実対角商における、元の零左成分と実自由右代表の全 dg End。 -/
abbrev DGOdotQuotientEnd := (dgOdotQuotientInput R d).endObject

/-- 元の右代数の指定対象の全 End から、同じ実対角商 End への実 dg 射。 -/
def dgOdotRightEndMap :
    DGFunctor R (EndomorphismObject (dgOdotInputRightPoint R d)) (DGOdotQuotientEnd R d) :=
  dgSmallPerfectSquareRightEndMap R (A) (C) (D) (E) (L) (G) (p) (q)
    (dgOdotInput_dg_commutes R d) (dgOdotInputRightPoint R d)

end SerrePositivity.KST.SConstruction
