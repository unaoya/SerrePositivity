module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DeformationHomNaturality
/-!
概要：制限上の指定合成子正方形を、同じ変形比較の全関手正方形へ移す。
方針：変形円柱と二つの指定同型の自然性、および前後合成の関手性を使う。
規約：同じ指定比較を保持する。使われ方：K-flat kernel 合成比較の二経路の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
/-- 指定比較の後合成の射は、同じ制限比較と変形円柱の通常後続像。 -/
lemma deformationComparison_postcomp_hom {A D B C Y : SSet.{u}}
    [Quasicategory Y]
    (L : A ⟶ D) (I : D ⟶ A) (H : SSet.Homotopy (L ≫ I) (𝟙 A))
    (K : D ⟶ C) (F : A ⟶ B) (M : B ⟶ C) (U : C ⟶ Y)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K (I ≫ F ≫ M)) (xi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ K) (F ≫ M))
    (hx : xi.hom = (r.precomp L).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H (F ≫ M)))) :
    (xi.postcomp U).hom = ((r.postcomp U).precomp L).hom ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H ((F ≫ M) ≫ U))) := by
  have hp : (xi.postcomp U).hom = ((r.precomp L).postcomp U).hom ≫
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H (F ≫ M)) U)) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom,
      CategoryTheory.Functor.map_comp] using! congrArg
        (fun m => (hoFunctor.map ((ihom A).map U)).toFunctor.map m) hx
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_postcomp] at hp
  rw [eq_of_heq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy_postcomp_hom_heq L I H (F ≫ M) U)] at hp
  exact hp
/-- 元の制限上の合成子正方形と同じ変形比較から、全関手射の二経路の一致を得る。 -/
lemma deformationCompositionSquare_hom {A D B C Y : SSet.{u}}
    [Quasicategory A] [Quasicategory Y]
    (L : A ⟶ D) (I : D ⟶ A) (H : SSet.Homotopy (L ≫ I) (𝟙 A))
    (K : D ⟶ C) (F : A ⟶ B) (M : B ⟶ C) (U : C ⟶ Y)
    (Kc : D ⟶ Y) (T : B ⟶ Y) (V : A ⟶ Y)
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso K (I ≫ F ≫ M)) (rc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso Kc (I ≫ V))
    (xi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ K) (F ≫ M)) (xic : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (L ≫ Kc) V)
    (y : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (M ≫ U) T) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F ≫ T) V)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (K ≫ U) Kc)
    (hx : xi.hom = (r.precomp L).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H (F ≫ M))))
    (hxc : xic.hom = (rc.precomp L).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H V)))
    (hc : c.hom ≫ rc.hom = (r.postcomp U).hom ≫ (y.precomp (I ≫ F)).hom ≫
      (a.precomp I).hom) :
    (c.precomp L).hom ≫ xic.hom = (xi.postcomp U).hom ≫ (y.precomp F).hom ≫ a.hom := by
  let d (W : A ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (L ≫ I ≫ W) W :=
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy L I H W))
  have hp : (xi.postcomp U).hom = ((r.postcomp U).precomp L).hom ≫ d ((F ≫ M) ≫ U) :=
    deformationComparison_postcomp_hom L I H K F M U r xi hx
  have hn : d ((F ≫ M) ≫ U) ≫ (y.precomp F).hom =
      ((y.precomp (I ≫ F)).precomp L).hom ≫ d (F ≫ T) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_precomp y F I] using!
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy_naturality L I H (y.precomp F)
  have ha : d (F ≫ T) ≫ a.hom = ((a.precomp I).precomp L).hom ≫ d V :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentHomotopy_naturality L I H a
  have hcp : (c.precomp L).hom ≫ (rc.precomp L).hom =
      ((r.postcomp U).precomp L).hom ≫ ((y.precomp (I ≫ F)).precomp L).hom ≫
        ((a.precomp I).precomp L).hom := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_precomp_hom, CategoryTheory.Functor.map_comp] using!
      congrArg (fun m => (hoFunctor.map ((pre L).app Y)).toFunctor.map m) hc
  rw [hp]
  symm
  calc
    _ = ((r.postcomp U).precomp L).hom ≫
        (d ((F ≫ M) ≫ U) ≫ (y.precomp F).hom) ≫ a.hom := by
      simp only [Category.assoc]
    _ = ((r.postcomp U).precomp L).hom ≫
        (((y.precomp (I ≫ F)).precomp L).hom ≫ d (F ≫ T)) ≫ a.hom := by rw [hn]
    _ = (((r.postcomp U).precomp L).hom ≫
        ((y.precomp (I ≫ F)).precomp L).hom) ≫ (d (F ≫ T) ≫ a.hom) := by
      simp only [Category.assoc]
    _ = (((r.postcomp U).precomp L).hom ≫
        ((y.precomp (I ≫ F)).precomp L).hom) ≫
        (((a.precomp I).precomp L).hom ≫ d V) := by rw [ha]
    _ = (c.precomp L).hom ≫ (rc.precomp L).hom ≫ d V := by
      simpa only [Category.assoc] using!
        (congrArg (fun m => m ≫ d V) hcp).symm
    _ = (c.precomp L).hom ≫ xic.hom := by rw [hxc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
