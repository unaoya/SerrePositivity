module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.KoszulModel
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.ExistsUnique
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Algebra.Defs

public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleComplete.Basic
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve



public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.IntegralPerfectoid
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal


public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
主元の導来完備化の環と延長の普遍性

可換環の実際の導来完備化と導来対象を用いる。
-/

universe u

/-! ## Perfectoid 化界面の通常の添字圏（旧 PerfectoidizationInterface/Setup.lean）

概要：同じ宇宙の可換代数、導来 p 完備な代数、perfectoid 標的の圏を定める。
方針：可換環の under 圏と充満部分圏を用いる。
規約：台環は Type u、圏の対象は Type (u+1)。巨大極限の存在は要求しない。
使われ方：E3 界面の始域と BS 著者版 Proposition 8.5 の制限した添字圏。
-/

@[expose] public noncomputable section Completion

namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory
open SerrePositivity.DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (p : ℕ)

/-- S の実際の導来 p 完備化の H⁰ 環。 -/
def completionRing (S : CommRingCat.{u}) : CommRingCat.{u} := by
  letI := principalCompletionCommRing S (p : S)
  exact CommRingCat.of (PrincipalCompletionH0 S (p : S))

/-- 元の Koszul 完備化単位を環の射として保持する。 -/
def completionUnit (S : CommRingCat.{u}) : S ⟶ completionRing p S := by
  letI := principalCompletionCommRing S (p : S)
  exact CommRingCat.ofHom (principalCompletionUnitRingHom S (p : S))

/-- 離散標的の完備性を、指定された元の環準同型に沿って制限する。 -/
theorem complete_along_map {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    letI := f.hom.toAlgebra; IsModuleComplete S (p : S) (ModuleCat.of S T) := by
  letI := f.hom.toAlgebra
  apply (isModuleComplete_algebraMap_iff S T (p : S) T).mp
  simpa only [map_natCast] using hT

/-- 完備な離散環への射は、指定された H⁰ 完備化単位に沿って一意に延長する。 -/
theorem completion_existsUnique {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) :
    ∃! g : completionRing p S ⟶ T, completionUnit p S ≫ g = f := by
  letI := principalCompletionCommRing S (p : S)
  obtain ⟨g, hg, hu⟩ := principalCompletion_existsUnique_ringHom S (p : S) T f.hom
    (complete_along_map p f hT)
  refine ⟨CommRingCat.ofHom g, ?_, ?_⟩
  · exact CommRingCat.hom_ext hg
  · intro k hk
    apply CommRingCat.hom_ext
    apply hu k.hom
    exact congrArg (fun (q : S ⟶ T) => q.hom) hk

/-- 完備標的への延長を選ぶ。 -/
def completionLift {S T : CommRingCat.{u}} (f : S ⟶ T)
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T)) : completionRing p S ⟶ T :=
  (completion_existsUnique p f hT).choose

/-- 完備標的への二射は、元の単位との合成で検出できる。 -/
theorem completion_hom_ext {S T : CommRingCat.{u}}
    (hT : IsModuleComplete T (p : T) (ModuleCat.of T T))
    {f g : completionRing p S ⟶ T}
    (h : completionUnit p S ≫ f = completionUnit p S ≫ g) : f = g :=
  (completion_existsUnique p (completionUnit p S ≫ f) hT).unique rfl h.symm

end SerrePositivity.BhattScholze.PerfectoidizationInterface

end Completion

/-! ## H⁰ の環構造と単位付き導来極限錐のデータ（旧 PerfectoidizationInterface/LimitData.lean）

概要：底の導来対象と無関係な環構造を許さず、辺と射影の乗法整合性を記録する。
方針：通常の R 代数の関手と加群の比較同型を持ち、実際の join 錐の脚を照合する。
規約：単位との両立は図式上の slice の辺として保持する。
使われ方：E3 界面の h0 と limitCone の型。
-/

