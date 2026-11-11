module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DeformationFunctorDescentHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomWhiskerExchange
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation
/-!
概要：制限比較と変形降下を通る四角形を、元の augmentation の後続像へ同定する。
方針：指定同型の交換則と、同じ変形円柱の前後合成の一致を使う。
規約：生の円柱の可逆性は仮定しない。使われ方：K-flat kernel 比較の二経路照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
/-- 制限比較と変形降下の四角形は、同じ実 augmentation の後続像へ一致する。 -/
lemma deformationRestrictionSquare_hom {A B C Y : SSet.{u}}
    [Quasicategory B] [Quasicategory C] [Quasicategory Y]
    (M : B ⟶ C) (J : C ⟶ B) (b : SSet.Homotopy (M ≫ J) (𝟙 B))
    (K : A ⟶ C) (f : A ⟶ B) (Q : C ⟶ Y) (V : B ⟶ Y)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K (f ≫ M)) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso Q (J ≫ V))
    (xi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (M ≫ Q) V) (H : SSet.Homotopy (K ≫ J) f)
    (hxi : xi.hom = (s.precomp M).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy M J b V)))
    (hr : (r.postcomp J).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp b f)) =
        Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) :
    (r.postcomp Q).hom ≫ (xi.precomp f).hom =
      (s.precomp K).hom ≫ Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H V)) := by
  have hex := congrArg Iso.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorIso_whisker_exchange r s)
  simp only [Iso.trans_hom] at hex
  have hx : (xi.precomp f).hom = ((s.precomp M).precomp f).hom ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy M J b V) f)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom, Functor.map_comp]
      using! congrArg (fun m => (hoFunctor.map ((pre f).app Y)).toFunctor.map m) hxi
  have hp : ((r.postcomp J).postcomp V).hom ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp b f) V)) =
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H V)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, Functor.map_comp]
      using! congrArg (fun m => (hoFunctor.map ((ihom A).map V)).toFunctor.map m) hr
  have hb : HEq (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy M J b V) f)))
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp b f) V))) := by
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomotopyHom_heq_of_raw_eq _ _ (Category.assoc _ _ _).symm
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp] at hx
  rw [hx, ← Category.assoc, hex, Category.assoc]
  congr 1
  rw [← _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp, eq_of_heq hb]
  exact hp
end SerrePositivity.InfinityCategories.Project.DerivedCategories
