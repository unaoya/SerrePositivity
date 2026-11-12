module
public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
概要：次数ごと単射で全要素を覆う filtered cocone の strict 余極限性。
方針：共通上界で等式を反映し、標準余極限からの比較射を全単射にする。
規約：κ-compact 性や native 余極限の比較は使わない。
使われ方：D-8 d の実部分 cell 加群の合併。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded

def dgKappaFilteredModuleUnionIsColimit (R : Type u) [CommRing R]
    {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat.{u} R)
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

def dgKappaModuleFilteredUnionIsColimit (R : Type u) [CommRing R]
    (D : Type v) [DGCategory R D] [Small.{u} D]
    {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCategory R D)
    (c : Cocone F)
    (hm : ∀ j x q, Mono (((moduleEvaluation R D x).map (c.ι.app j)).f q))
    (hs : ∀ x q (z : ((moduleEvaluation R D x).obj c.pt).X q),
      ∃ j a, ((moduleEvaluation R D x).map (c.ι.app j)).f q a = z) : IsColimit c := by
  let d := colimit.desc F c
  have hi : IsIso d := moduleIsIso_of_evaluations R D d (by
    intro x
    have hq (q : ℤ) : IsIso (((moduleEvaluation R D x).map d).f q) := by
      let E := moduleEvaluation R D x ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℤ) q
      have hc := dgKappaFilteredModuleUnionIsColimit R (F ⋙ E) (E.mapCocone c)
        (fun j => (ModuleCat.mono_iff_injective _).mp (hm j x q)) (hs x q)
      have hc0 := isColimitOfPreserves E (colimit.isColimit F)
      let e := hc0.coconePointUniqueUpToIso hc
      have he : E.map d = e.hom := by
        apply hc0.hom_ext
        intro j
        have hf : (E.mapCocone (colimit.cocone F)).ι.app j ≫ E.map d =
            (E.mapCocone c).ι.app j := by
          simpa only [E.map_comp] using! congrArg E.map (colimit.ι_desc c j)
        exact hf.trans (hc0.comp_coconePointUniqueUpToIso_hom hc j).symm
      change IsIso (E.map d)
      rw [he]
      infer_instance
    letI := hq
    exact HomologicalComplex.Hom.isIso_of_components _)
  letI := hi
  exact IsColimit.ofIsoColimit (colimit.isColimit F)
    (Cocone.ext (asIso d) (fun j => colimit.ι_desc c j))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
