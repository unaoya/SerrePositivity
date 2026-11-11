module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses

/-!
概要：Kan 標的の同じ円柱から作る同型の後合成を、元の円柱の像の類へ戻す。
方針：後合成の h Fun 作用と、raw な定値円柱の恒等性を使う。
規約：元の円柱と像を保持する。使われ方：初期 Hom 比較の評価の恒等性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 関手同型の後合成の射は、同じ h Fun の後合成関手による像。 -/
lemma functorIso_postcomp_hom {T E B : SSet.{u}} {a b : T ⟶ E}
    (I : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso a b) (q : E ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp I q).hom = (hoFunctor.map ((ihom T).map q)).toFunctor.map I.hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp, Iso.trans_hom, Iso.symm_hom, eqToIso.inv, eqToIso.hom,
    eqToHom_refl, Functor.mapIso_hom, Category.id_comp, Category.comp_id]

/-- 同じ円柱の同型を後合成した射は、同じ円柱の後合成の辺の類である。 -/
lemma homotopyIso_postcomp_hom {T E B : SSet.{u}} [KanComplex E]
    {a b : T ⟶ E} (H : SSet.Homotopy a b) (q : E ⟶ B) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H) q).hom =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H q)) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom H q).symm

/-- 同じ円柱の像が全時刻定値なら、像の同型の射もその同じ全族の恒等射。 -/
lemma homotopyIso_postcomp_constant_arrow {T E B : SSet.{u}} [KanComplex E]
    {a b : T ⟶ E} (H : SSet.Homotopy a b) (q : E ⟶ B) (z : T ⟶ B)
    (hH : H.h ≫ q = fst T Δ[1] ≫ z) :
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy H) q).hom =
      Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex z))) := by
  rw [homotopyIso_postcomp_hom]
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H q) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl z) hH
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom] at h
  exact h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
