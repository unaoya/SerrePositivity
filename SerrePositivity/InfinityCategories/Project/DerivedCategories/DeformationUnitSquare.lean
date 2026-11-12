module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DeformationRetractTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DeformationRestrictionSquare
/-!
概要：同じ augmentation と変形比較を使い、元の指定単位の整合性を証明する。
方針：戻り同型の補助三角式と、元の円柱・指定同型の全関手交換を使う。
規約：既存の指定単位を変更しない。使われ方：K-flat kernel の単位比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
variable {A D : SSet.{u}} [Quasicategory A] [Quasicategory D]
  (L : A ⟶ D) (I : D ⟶ A) (H : SSet.Homotopy (L ≫ I) (𝟙 A))
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (I ≫ L) (𝟙 D))
  (K : D ⟶ D) (N : A ⟶ A) (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K (I ≫ N ≫ L))
  (HP : SSet.Homotopy (K ≫ I) (I ≫ N))
  (ht : Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H L)) = (e.precomp L).hom)
  (hr : (r.postcomp I).hom ≫ Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (I ≫ N))) =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy HP))
include ht hr in
/-- 同じ augmentation 正方形の制限比較は、戻り同型の逆と円柱の通常像で表される。 -/
lemma deformationIdentityFactor_hom :
    r.hom = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.symm K).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp HP L)) := by
  have hx : (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex L))).hom =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.symm L).hom ≫ Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H L)) := by
    rw [ht]
    change 𝟙 _ = (e.precomp L).inv ≫ (e.precomp L).hom
    exact (Iso.inv_hom_id _).symm
  have hm := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationRestrictionSquare_hom L I H K (I ≫ N) (𝟙 D) L r e.symm
    (Iso.refl _) HP hx hr
  have hm' : r.hom ≫ 𝟙 _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.symm K).hom ≫
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp HP L)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_id, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom,
      Iso.refl_hom, CategoryTheory.Functor.map_id] using! hm
  simpa only [Category.comp_id] using! hm'
include ht hr in
/-- 元の指定単位は、同じ制限比較・通常単位・augmentation 戻り同型の経路に一致。 -/
lemma deformationUnitFactor_hom (u : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso N (𝟙 A)) (v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K (𝟙 D))
    (hv : (v.postcomp I).hom = Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy HP) ≫ (u.precomp I).hom) :
    v.hom = r.hom ≫ ((u.precomp I).postcomp L).hom ≫ e.hom := by
  have hp0 : ((v.postcomp I).postcomp L).hom =
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp HP L)) ≫
      ((u.precomp I).postcomp L).hom := by
    have hh := congrArg (fun m => (hoFunctor.map ((ihom D).map L)).toFunctor.map m) hv
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom,
      CategoryTheory.Functor.map_comp] using! hh
  have hp := hp0
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp] at hp
  have hc := congrArg Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_whisker_exchange v e)
  simp only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_id, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_precomp_id_hom] at hc
  rw [deformationIdentityFactor_hom L I H e K N r HP ht hr]
  symm
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.symm K).hom ≫ (v.postcomp (I ≫ L)).hom ≫ e.hom := by
      rw [hp]
      simp only [Category.assoc]
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.symm K).hom ≫ (e.precomp K).hom ≫ v.hom := by rw [hc]
    _ = v.hom := by
      change (e.precomp K).inv ≫ (e.precomp K).hom ≫ v.hom = _
      rw [Iso.inv_hom_id_assoc]
include ht hr in
/-- 元の変形比較と通常単位を通る経路は、元の指定単位の分解制限に一致。 -/
lemma deformationUnitSquare_hom (u : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso N (𝟙 A)) (v : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K (𝟙 D))
    (xi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ K) (N ≫ L))
    (hv : (v.postcomp I).hom = Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy HP) ≫ (u.precomp I).hom)
    (hx : xi.hom = (r.precomp L).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H (N ≫ L)))) :
    xi.hom ≫ (u.postcomp L).hom = (v.precomp L).hom := by
  have hn : Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H (N ≫ L))) ≫ (u.postcomp L).hom =
      (((u.postcomp L).precomp I).precomp L).hom ≫
        Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H L)) := by
    simpa only [Category.id_comp] using!
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy_naturality L I H (u.postcomp L)
  rw [hx, Category.assoc, hn, ht]
  have hf : (r.precomp L).hom ≫ (((u.precomp I).postcomp L).precomp L).hom ≫
      (e.precomp L).hom = (v.precomp L).hom := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom, CategoryTheory.Functor.map_comp] using!
      (congrArg (fun m => (hoFunctor.map ((pre L).app D)).toFunctor.map m)
        (deformationUnitFactor_hom L I H e K N r HP ht hr u v hv)).symm
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp u I L] at hf
  exact hf
end SerrePositivity.InfinityCategories.Project.DerivedCategories
