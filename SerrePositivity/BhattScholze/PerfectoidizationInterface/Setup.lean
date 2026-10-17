module

public import SerrePositivity.CommutativeAlgebra.IntegralPerfectoid
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Module
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! # Perfectoid 化界面の通常の添字圏

概要：同じ宇宙の可換代数、導来 p 完備な代数、perfectoid 標的の圏を定める。
方針：可換環の under 圏と充満部分圏を用いる。
規約：台環は Type u、圏の対象は Type (u+1)。巨大極限の存在は要求しない。
使われ方：E3 界面の始域と Prop 8.5 の制限した添字圏。
-/

@[expose] public section
universe u
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory
open SerrePositivity.DerivedCompletion

/-- Type u の通常の可換 R 代数の圏。構造射をデータとして保持する。 -/
abbrev A_R (R : Type u) [CommRing R] := Under (CommRingCat.of R)

/-- 通常の R 代数を、元の代数構造の射とともに束ねる。 -/
def ofAlgebra (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : A_R R :=
  Under.mk (CommRingCat.ofHom (algebraMap R S))

/-- 始域に課す導来 p 完備性。通常の p 進完備性へ置き換えない。 -/
def completeProperty (R : Type u) [CommRing R] (p : ℕ) : ObjectProperty (A_R R) :=
  fun S => IsModuleComplete S.right (p : S.right) (ModuleCat.of S.right S.right)

/-- 導来 p 完備な通常の R 代数の充満部分圏。 -/
abbrev C_R (R : Type u) [CommRing R] (p : ℕ) := (completeProperty R p).FullSubcategory

/-- 完備性の条件だけを忘れる包含関手。 -/
abbrev completeInclusion (R : Type u) [CommRing R] (p : ℕ) : C_R R p ⥤ A_R R :=
  (completeProperty R p).ι

/-- S の下の環のうち、標的が perfectoid であるという性質。 -/
def perfectoidTargetProperty (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) :
    ObjectProperty (Under S) := fun T => IsIntegralPerfectoid T.right p

/-- Type u の perfectoid 標的 S → T の圏。射の向きを反転しない。 -/
abbrev PerfUnder_u (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) :=
  (perfectoidTargetProperty p S).FullSubcategory

/-- perfectoid 条件を忘れ、元の S 上の環を取り出す。 -/
abbrev perfectoidTargetInclusion (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) :
    PerfUnder_u p S ⥤ Under S := (perfectoidTargetProperty p S).ι

/-- perfectoid 標的の R 作用は R → S → T の合成で定める。 -/
def targetAlgebra (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (S : A_R R) :
    PerfUnder_u p S.right ⥤ A_R R :=
  perfectoidTargetInclusion p S.right ⋙ Under.map S.hom

/-- 通常の代数圏の nerve。対象宇宙 u+1 に置く。 -/
abbrev algebraNerve (R : Type u) [CommRing R] : SSet.{u + 1} := nerve (A_R R)

/-- 制限した perfectoid 標的圏の nerve。 -/
abbrev perfectoidTargetNerve (p : ℕ) [Fact p.Prime] (S : CommRingCat.{u}) : SSet.{u + 1} :=
  nerve (PerfUnder_u p S)

end SerrePositivity.BhattScholze.PerfectoidizationInterface
