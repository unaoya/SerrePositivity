module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.Comparisons
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# 主完備化 H⁰ の可換環上の関手

## 概要
自然数 p による主完備化の H⁰ を環と基底つきの環に施す。

## 方針
主完備化の普遍性で誘導射の合成と恒等を確かめる。

## 規約
完備化の単位は Koszul 模型の標準射。

## 使われ方
多項式の pd Čech 模型の各項の p 完備化。
-/

public noncomputable section

open CategoryTheory

universe u

namespace SerrePositivity.DerivedCompletion

variable (p : ℕ)

/-- 可換環の主完備化の H⁰ 環。 -/
def principalCompletionRingCat (R : CommRingCat.{u}) : CommRingCat.{u} :=
  letI := principalCompletionCommRing R (p : R)
  CommRingCat.of (PrincipalCompletionH0 R (p : R))

/-- 主完備化への単位。 -/
def principalCompletionRingCatUnit (R : CommRingCat.{u}) : R ⟶ principalCompletionRingCat p R :=
  letI := principalCompletionCommRing R (p : R)
  CommRingCat.ofHom (principalCompletionUnitRingHom R (p : R))

private def ringCatMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    principalCompletionRingCat p R ⟶ principalCompletionRingCat p S :=
  letI := principalCompletionCommRing R (p : R)
  letI := principalCompletionCommRing S (p : S)
  CommRingCat.ofHom (principalCompletionMap f.hom (p : R) (p : S) (map_natCast f.hom p))

private theorem ringCatMap_comp_unit {R S : CommRingCat.{u}} (f : R ⟶ S) :
    principalCompletionRingCatUnit p R ≫ ringCatMap p f = f ≫ principalCompletionRingCatUnit p S := by
  apply CommRingCat.hom_ext
  exact principalCompletionMap_comp f.hom (p : R) (p : S) (map_natCast f.hom p)

private theorem ringCat_hom_ext {R S : CommRingCat.{u}}
    {f g : principalCompletionRingCat p R ⟶ principalCompletionRingCat p S}
    (h : principalCompletionRingCatUnit p R ≫ f = principalCompletionRingCatUnit p R ≫ g) :
    f = g := by
  let := principalCompletionCommRing R (p : R)
  let := principalCompletionCommRing S (p : S)
  let a := principalCompletionUnitRingHom R (p : R)
  let z : R →+* PrincipalCompletionH0 S (p : S) := f.hom.comp a
  have hc : letI := z.toAlgebra
      IsModuleComplete R (p : R) (ModuleCat.of R (PrincipalCompletionH0 S (p : S))) := by
    let := z.toAlgebra
    change IsModuleComplete R (p : R) (ModuleCat.of R (PrincipalCompletionH0 S (p : S)))
    apply (isModuleComplete_algebraMap_iff R (PrincipalCompletionH0 S (p : S)) (p : R)
      (PrincipalCompletionH0 S (p : S))).mp
    change IsModuleComplete (PrincipalCompletionH0 S (p : S)) (z (p : R)) _
    have hp : z (p : R) = principalCompletionUnitRingHom S (p : S) (p : S) :=
      (map_natCast z p).trans (map_natCast (principalCompletionUnitRingHom S (p : S)) p).symm
    rw [hp]
    have H := principalCompletion_isModuleComplete_unit (p : S)
    rw [isModuleComplete_iff_recurrence_bijective] at H ⊢
    exact H
  apply CommRingCat.hom_ext
  exact (principalCompletion_existsUnique_ringHom R (p : R) _ z hc).unique rfl
    (congrArg CommRingCat.Hom.hom h).symm

/-- H⁰ 主完備化を施す可換環の関手。 -/
def principalCompletionRingFunctor : CommRingCat.{u} ⥤ CommRingCat.{u} where
  obj := principalCompletionRingCat p
  map := ringCatMap p
  map_id R := by
    apply ringCat_hom_ext p
    rw [ringCatMap_comp_unit, Category.id_comp, Category.comp_id]
  map_comp f g := by
    apply ringCat_hom_ext p
    rw [ringCatMap_comp_unit, ← Category.assoc, ringCatMap_comp_unit,
      Category.assoc, Category.assoc, ringCatMap_comp_unit]

/-- 係数環を保ち、対象の環に H⁰ 主完備化を施す。 -/
def principalCompletionUnder (K : CommRingCat.{u}) : Under K ⥤ Under K where
  obj X := Under.mk (X.hom ≫ principalCompletionRingCatUnit p X.right)
  map f := Under.homMk (ringCatMap p f.right) (by
    change (_ ≫ principalCompletionRingCatUnit p _) ≫ ringCatMap p f.right =
      _ ≫ principalCompletionRingCatUnit p _
    rw [Category.assoc, ringCatMap_comp_unit, ← Category.assoc, Under.w])
  map_id X := by
    ext1
    exact (principalCompletionRingFunctor p).map_id X.right
  map_comp f g := by
    ext1
    exact (principalCompletionRingFunctor p).map_comp f.right g.right

end SerrePositivity.DerivedCompletion
