module
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
概要：filtered な包含余錐の網羅性から余極限性を得る。
方針：標準余極限の二要素を共通段へ移し、包含の単射性で比較を全単射にする。
規約：native 余極限と κ-compact 性は使わない。
使われ方：単体次元の実部分複体の合併。
-/
@[expose] public section
noncomputable section
universe u w
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits

def dgBarFilteredModuleUnionIsColimit (R : Type u) [CommRing R]
    {J : Type w} [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat.{u} R)
    [HasColimit F] [PreservesColimit F (forget (ModuleCat.{u} R))]
    (c : Cocone F) (hm : ∀ j, Function.Injective (c.ι.app j))
    (hs : ∀ z : c.pt, ∃ j a, c.ι.app j a = z) : IsColimit c := by
  let d := colimit.desc F c
  have fac (j : J) (a : F.obj j) : d (colimit.ι F j a) = c.ι.app j a :=
    congrArg (fun f => f a) (colimit.ι_desc c j)
  have hd : Function.Bijective d := by
    constructor
    · intro a b hab
      obtain ⟨i, x, rfl⟩ := Concrete.colimit_exists_rep F a
      obtain ⟨j, y, rfl⟩ := Concrete.colimit_exists_rep F b
      rw [fac, fac] at hab
      let k := IsFiltered.max i j
      let f := IsFiltered.leftToMax i j
      let g := IsFiltered.rightToMax i j
      apply Concrete.colimit_rep_eq_of_exists F x y
      refine ⟨k, f, g, hm k ?_⟩
      have hf := congrArg (fun h => h x) (c.w f)
      have hg := congrArg (fun h => h y) (c.w g)
      exact hf.trans (hab.trans hg.symm)
    · intro z
      obtain ⟨j, a, ha⟩ := hs z
      exact ⟨colimit.ι F j a, (fac j a).trans ha⟩
  letI : IsIso d := (ConcreteCategory.isIso_iff_bijective d).mpr hd
  exact IsColimit.ofIsoColimit (colimit.isColimit F)
    (Cocone.ext (asIso d) (fun j => colimit.ι_desc c j))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
