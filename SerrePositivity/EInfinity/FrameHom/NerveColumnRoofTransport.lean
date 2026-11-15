module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoConstantFamily
public import SerrePositivity.EInfinity.SimplicialLocalization.RoofPrefixColumnRoof
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeFamilyUnderlying
public import SerrePositivity.EInfinity.FrameHom.NerveColumnRoofNaturality

/-! 元の全roofを同じ全局所化三角形で共役し、指定成分の定値族へ戻す。 -/

@[expose] public section
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.EInfinity.SimplicialLocalization
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.EInfinity.FrameHom
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.EInfinity.FrameHom.NerveColumn

/-- 元の全三角形・指定成分・roofの自然性を同じ全族で保持する法則。 -/
lemma roof_conjugation {I C : Type u} [Category.{u} I] [Category.{u} C]
    {E : SSet.{u}} [Quasicategory E] {F G : nerve C ⟶ E} (e : FunctorIso F G)
    (V : I ⥤ C) {X Y : C} (p : V ⟶ (Functor.const I).obj X)
    (hpF : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated)
    (hpG : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map G).toTruncated)
    (s : V ⟶ (Functor.const I).obj Y) :
    (e.precomp (nerveMap ((Functor.const I).obj X))).inv ≫
      (NerveColumn.augmentationIso F V p hpF).inv ≫ NerveColumn.hom F s ≫
      (e.precomp (nerveMap ((Functor.const I).obj Y))).hom =
      (NerveColumn.augmentationIso G V p hpG).inv ≫ NerveColumn.hom G s := by
  apply (cancel_epi (e.precomp (nerveMap ((Functor.const I).obj X))).hom).mp
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using
    (NerveColumn.roof_naturality e V p hpF hpG s).symm
/-- 元の全三角形・指定成分・roofの自然性を同じ全族で保持する法則。 -/
lemma constantRestriction_iso_arrow {I C : Type u} [Category.{u} I] [Category.{u} C]
    {E : SSet.{u}} [Quasicategory E] {F G : nerve C ⟶ E} (e : FunctorIso F G) (c : C) :
    Arrow.mk (e.precomp (nerveMap ((Functor.const I).obj c))).hom =
      Arrow.mk (constantFunctorHomMap (nerve I) (e.app (nerveVertex c)).hom) := by
  rw [nerveMap_const]
  have h := congrArg Arrow.mk (sameFunctorIso_constant_family (nerve I) e (nerveVertex c))
  simpa only [constantFunctorCompIso, eqToIso.inv, eqToIso.hom, ← Category.assoc,
    Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom] using h
/-- 元の全三角形・指定成分・roofの自然性を同じ全族で保持する法則。 -/
lemma constantRestriction_iso_inv_arrow {I C : Type u} [Category.{u} I] [Category.{u} C]
    {E : SSet.{u}} [Quasicategory E] {F G : nerve C ⟶ E} (e : FunctorIso F G) (c : C) :
    Arrow.mk (e.precomp (nerveMap ((Functor.const I).obj c))).inv =
      Arrow.mk (constantFunctorHomMap (nerve I) (e.app (nerveVertex c)).inv) := by
  simpa only [SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_symm, FunctorIso.app_symm, Iso.symm_hom] using
    (constantRestriction_iso_arrow (I := I) e.symm c)
/-- 元の全三角形・指定成分・roofの自然性を同じ全族で保持する法則。 -/
lemma roof_constant_conjugation_arrow {I C : Type u} [Category.{u} I] [Category.{u} C]
    {E : SSet.{u}} [Quasicategory E] {F G : nerve C ⟶ E} (e : FunctorIso F G)
    (V : I ⥤ C) {X Y : C} (p : V ⟶ (Functor.const I).obj X)
    (hpF : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated)
    (hpG : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map G).toTruncated)
    (s : V ⟶ (Functor.const I).obj Y)
    (a : FunctorHom (SSet.const (F.app (Opposite.op ⦋0⦌) (nerveVertex X)) : nerve I ⟶ E)
      (SSet.const (F.app (Opposite.op ⦋0⦌) (nerveVertex Y))))
    (ha : Arrow.mk a = Arrow.mk ((NerveColumn.augmentationIso F V p hpF).inv ≫ NerveColumn.hom F s)) :
    Arrow.mk (constantFunctorHomMap (nerve I) (e.app (nerveVertex X)).inv ≫ a ≫
      constantFunctorHomMap (nerve I) (e.app (nerveVertex Y)).hom) =
      Arrow.mk ((NerveColumn.augmentationIso G V p hpG).inv ≫ NerveColumn.hom G s) := by
  have hx := constantRestriction_iso_inv_arrow (I := I) e X
  have hy := constantRestriction_iso_arrow (I := I) e Y
  have hm := RoofPrefix.comp_arrow_eq _ _ _ _ hx.symm ha
  have ht := RoofPrefix.comp_arrow_eq _ _ _ _ hm hy.symm
  have hr := congrArg Arrow.mk (roof_conjugation e V p hpF hpG s)
  simp only [Category.assoc] at ht
  exact ht.trans hr

end SerrePositivity.EInfinity.FrameHom.NerveColumn

end
