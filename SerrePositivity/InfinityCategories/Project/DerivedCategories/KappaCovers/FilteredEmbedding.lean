module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers.FilteredUnion

/-!
概要：filtered な部分加群の包含を、strict 余極限からの包含へ延ばす。
方針：二つの余極限要素を共通の有限段へ移し、その段の単射性を使う。
規約：網羅性は要求しない。
使われ方：D-8 d の部分 cell 列の余極限の単射性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded

lemma dgKappaFilteredModuleCoconeDesc_injective (R : Type u) [CommRing R]
    {J : Type w} [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat.{u} R)
    [PreservesColimit F (forget (ModuleCat.{u} R))]
    {c₀ c : Cocone F} (hc₀ : IsColimit c₀) (hm : ∀ j, Function.Injective (c.ι.app j)) :
    Function.Injective (hc₀.desc c) := by
  intro a b hab
  obtain ⟨i, x, rfl⟩ := Concrete.isColimit_exists_rep F hc₀ a
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep F hc₀ b
  have fac (k : J) (z : F.obj k) : hc₀.desc c (c₀.ι.app k z) = c.ι.app k z :=
    congrArg (fun f => f z) (hc₀.fac c k)
  rw [fac, fac] at hab
  let k := IsFiltered.max i j
  let f := IsFiltered.leftToMax i j
  let g := IsFiltered.rightToMax i j
  apply Concrete.isColimit_rep_eq_of_exists F x y
  refine ⟨k, f, g, hm k ?_⟩
  have hf := congrArg (fun h => h x) (c.w f)
  have hg := congrArg (fun h => h y) (c.w g)
  exact hf.trans (hab.trans hg.symm)

lemma dgKappaModuleFilteredCoconeDesc_degreewiseMono (R : Type u) [CommRing R]
    (D : Type v) [DGCategory R D] [Small.{u} D]
    {J : Type w} [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCategory R D)
    [HasColimit F]
    [∀ x q, PreservesColimit F
      (moduleEvaluation R D x ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℤ) q)]
    [∀ x q, PreservesColimit
      (F ⋙ (moduleEvaluation R D x ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℤ) q))
      (forget (ModuleCat.{u} R))]
    (c : Cocone F)
    (hm : ∀ j x q, Mono (((moduleEvaluation R D x).map (c.ι.app j)).f q))
    (x : D) (q : ℤ) :
    Mono (((moduleEvaluation R D x).map (colimit.desc F c)).f q) := by
  let E := moduleEvaluation R D x ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℤ) q
  have hc₀ := isColimitOfPreserves E (colimit.isColimit F)
  have he : E.map (colimit.desc F c) = hc₀.desc (E.mapCocone c) := by
    refine hc₀.uniq (E.mapCocone c) (E.map (colimit.desc F c)) ?_
    intro j
    simpa only [E.map_comp] using! congrArg E.map (colimit.ι_desc c j)
  apply (ModuleCat.mono_iff_injective _).mpr
  change Function.Injective (E.map (colimit.desc F c))
  rw [he]
  exact dgKappaFilteredModuleCoconeDesc_injective R _ hc₀
    (fun j => (ModuleCat.mono_iff_injective _).mp (hm j x q))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
