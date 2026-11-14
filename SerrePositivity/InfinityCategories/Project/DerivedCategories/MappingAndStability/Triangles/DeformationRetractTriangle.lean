module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.ResolutionComparisons.DeformationHomNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulPostcomposition
/-!
概要：同じ変形円柱からの戻り同型と、局所化前合成の三角式を証明する。
方針：同じ指定値と円柱の前後合成を全関手射の等式で照合する。
規約：既存の導来単位を変更しない。使われ方：K-flat 単位の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
/-- 充満忠実な像にある射は、合成関手の充満忠実性によって検出される。 -/
lemma functorMap_injective_on_full_image {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) (hF : F.FullyFaithful) (hFG : (F ⋙ G).FullyFaithful)
    {x y : C} (a b : F.obj x ⟶ F.obj y) (h : G.map a = G.map b) : a = b := by
  have hp : hF.preimage a = hF.preimage b := by
    apply hFG.map_injective
    simpa only [CategoryTheory.Functor.comp_map, hF.map_preimage] using! h
  calc
    a = F.map (hF.preimage a) := (hF.map_preimage a).symm
    _ = F.map (hF.preimage b) := congrArg (fun m => F.map m) hp
    _ = b := hF.map_preimage b
/-- 局所化前合成の像の全関手射の等式は、戻り包含への制限で反映される。 -/
lemma deformationRestrictionHom_injective {A D Y : SSet.{u}}
    [Quasicategory D] [Quasicategory Y]
    (L : A ⟶ D) (I : D ⟶ A) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (I ≫ L) (𝟙 D))
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre L).app Y)) {f g : D ⟶ Y} :
    Function.Injective (fun a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (L ≫ f) (L ≫ g) =>
      (SSet.mapHomotopyCategory ((pre I).app Y)).map a) := by
  let F := (hoFunctor.map ((pre L).app Y)).toFunctor
  let G := (hoFunctor.map ((pre I).app Y)).toFunctor
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (((pre L).app Y) ≫ ((pre I).app Y)) := by
    have hq := ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence.refl D).isQCatEquivalence.ofFunctorIso e.symm).precompose Y
    have he := hq.isFullyFaithful
    simpa only [pre_map, NatTrans.comp_app] using! he
  have hFG : (F ⋙ G).FullyFaithful := by
    have he : (hoFunctor.map (((pre L).app Y) ≫ ((pre I).app Y))).toFunctor = F ⋙ G := by
      rw [CategoryTheory.Functor.map_comp]
      rfl
    rw [← he]
    exact hc.toHoFullyFaithful
  intro a b hab
  exact functorMap_injective_on_full_image F G hL.toHoFullyFaithful hFG
    (x := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)) (y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g))
    a b hab
/-- 恒等への同じ戻り同型は自己前後合成の射が一致する。 -/
lemma functorIso_retract_self_whisker_hom {D : SSet.{u}} [Quasicategory D] {f : D ⟶ D}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f (𝟙 D)) : (e.postcomp f).hom = (e.precomp f).hom := by
  have h := congrArg Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_whisker_exchange e e)
  simp only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_id_hom] at h
  exact (cancel_mono e.hom).mp h
/-- 同じ変形円柱から回収した戻り同型は、分解後の三角式を満たす。 -/
lemma deformationRetractTriangle_hom {A D : SSet.{u}}
    [Quasicategory D]
    (L : A ⟶ D) (I : D ⟶ A) (H : SSet.Homotopy (L ≫ I) (𝟙 A))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (I ≫ L) (𝟙 D)) (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre L).app D))
    (he : (e.postcomp I).hom = Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H I))) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H L)) = (e.precomp L).hom := by
  apply deformationRestrictionHom_injective L I e hL (f := I ≫ L) (g := 𝟙 D)
  have hp : ((e.postcomp I).postcomp L).hom = Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H I) L)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom] using!
      congrArg (fun m => (hoFunctor.map ((ihom D).map L)).toFunctor.map m) he
  have hr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopyHom_heq_of_raw_eq
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H L) I)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H I) L)
    (Category.assoc _ _ _).symm
  have hpost := congrArg Iso.hom (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp e I L)
  have hpre := congrArg Iso.hom (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp e L I)
  have hh := eq_of_heq (hr.trans ((heq_of_eq hp.symm).trans
    ((heq_of_eq hpost).trans ((heq_of_eq (functorIso_retract_self_whisker_hom e)).trans
      (heq_of_eq hpre.symm)))))
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom] using! hh
end SerrePositivity.InfinityCategories.Project.DerivedCategories
