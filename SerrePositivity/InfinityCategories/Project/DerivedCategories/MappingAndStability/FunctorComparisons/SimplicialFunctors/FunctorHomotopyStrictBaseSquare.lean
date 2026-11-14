module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransportAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomotopyInputExchange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomotopyRawTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoTransportAlgebra
/-!
概要：基底上で恒等となる入力比較と全単体ホモトピーの交換則を簡約する。
方針：指定同型の後続像を同じ恒等射に同定し、非可逆な全関手射の右単位を相殺する。
規約：端点輸送と同じ指定射を保持する。使われ方：実分解比較の augmentation 正方形。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
/-- 型付きで右側が同じ恒等射なら、その後合成を厳密に相殺できる。 -/
lemma hom_comp_heq_of_right_id {C : Type u} [Category C]
    {a b c : C} (e : a ⟶ b) (d : b ⟶ c) (hc : b = c) (hd : HEq d (𝟙 b)) :
    HEq (e ≫ d) e := by
  subst c
  cases eq_of_heq hd
  exact heq_of_eq (Category.comp_id e)
/-- 指定入力同型が基底上で恒等なら、同じ全単体ホモトピーの交換正方形を相殺できる。 -/
lemma strictBaseHomotopySquare_heq {X Y B Z : SSet.{u}}
    [Quasicategory Y] [Quasicategory Z]
    {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (p : Y ⟶ B) (t : B ⟶ Z)
    (r : Y ⟶ Z) (H : SSet.Homotopy r (p ≫ t))
    (hg : g ≫ p = f ≫ p)
    (he : HEq (e.postcomp p) (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p))))) :
    HEq ((e.postcomp r).hom ≫ Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H g)))
      (Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H f))) := by
  let b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (f ≫ p) (f ≫ p) :=
    Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p)))
  have hp := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_heq_of_heq b (e.postcomp p) rfl hg.symm he t
  have hid : b.postcomp t = Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p ≫ t))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso]
    exact CategoryTheory.Functor.mapIso_refl _ _
  have hi : HEq (e.postcomp (p ≫ t))
      (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p ≫ t)))) :=
    (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_postcomp e p t).symm).trans
      (hp.trans (heq_of_eq hid))
  have hh : g ≫ p ≫ t = f ≫ p ≫ t := by
    simpa only [Category.assoc] using congrArg (fun m => m ≫ t) hg
  have hhom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq (e.postcomp (p ≫ t))
    (Iso.refl (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ p ≫ t)))) rfl hh hi
  have hc := hom_comp_heq_of_right_id
    (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H f)))
    (e.postcomp (p ≫ t)).hom
    (congrArg (fun m => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex m)) hh.symm) hhom
  exact (heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.iso_precomp_homotopy_exchange e H)).trans hc
end SerrePositivity.InfinityCategories.Project.DerivedCategories
