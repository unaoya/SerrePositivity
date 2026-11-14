module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomotopyRawTransport
/-!
概要：端点を明示した全関手射の異種等式を、前後合成の実作用へ移す。
方針：端点等式を消去し、同じホモトピー圏の関手で写す。
規約：元の全関手射を保つ。使われ方：kernel の結合子の経路比較。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
/-- 同じ全関手射の異種等式は、実前合成の作用で保たれる。 -/
lemma functorHom_precomp_heq {X Y Z : SSet.{u}} {f g f' g' : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (a' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g') (hf : f = f') (hg : g = g')
    (ha : HEq a a') (H : Z ⟶ X) :
    HEq ((SSet.mapHomotopyCategory ((pre H).app Y)).map a)
      ((SSet.mapHomotopyCategory ((pre H).app Y)).map a') := by
  subst f' g'
  cases eq_of_heq ha
  rfl
/-- 同じ全関手射の異種等式は、実後合成の作用で保たれる。 -/
lemma functorHom_postcomp_heq {X Y Z : SSet.{u}} {f g f' g' : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (a' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g') (hf : f = f') (hg : g = g')
    (ha : HEq a a') (H : Y ⟶ Z) :
    HEq ((SSet.mapHomotopyCategory ((ihom X).map H)).map a)
      ((SSet.mapHomotopyCategory ((ihom X).map H)).map a') := by
  subst f' g'
  cases eq_of_heq ha
  rfl
/-- 指定同型の射の異種等式を、同じ指定後合成同型の射へ移す。 -/
lemma functorIso_postcomp_hom_heq {X Y Z : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (a' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g') (hf : f = f') (hg : g = g')
    (ha : HEq e.hom a') (H : Y ⟶ Z) :
    HEq (e.postcomp H).hom ((SSet.mapHomotopyCategory ((ihom X).map H)).map a') := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_hom]
  exact functorHom_postcomp_heq e.hom a' hf hg ha H
/-- 指定同型の射の異種等式を、同じ指定前合成同型の射へ移す。 -/
lemma functorIso_precomp_hom_heq {X Y Z : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (a' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g') (hf : f = f') (hg : g = g')
    (ha : HEq e.hom a') (H : Z ⟶ X) :
    HEq (e.precomp H).hom ((SSet.mapHomotopyCategory ((pre H).app Y)).map a') := by
  exact functorHom_precomp_heq e.hom a' hf hg ha H
end SerrePositivity.InfinityCategories.Project.DerivedCategories
