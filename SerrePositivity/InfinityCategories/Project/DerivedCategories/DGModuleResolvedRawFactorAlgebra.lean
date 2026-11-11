module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedRawFactor
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
/-!
概要：生の全関手同型を同じ実出力分解へ送る操作は、恒等と合成を保つ。
方針：指定因数分解同型の共役表示と、同じ前後合成の代数則を使う。
規約：元の全関手圏の等式を証明する。使われ方：一般 kernel 比較の coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の全関手同型を出力分解へ送る操作は、同じ全関手圏で合成を保つ。 -/
lemma dgModuleResolvedInfinity_isoOfRawFunctorIso_trans
    (F G H : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E))
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G))
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isoOfRawFunctorIso R C E F H (a ≪≫ b) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isoOfRawFunctorIso R C E F G a ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isoOfRawFunctorIso R C E G H b := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isoOfRawFunctorIso
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_trans]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
/-- 元の全関手同型を出力分解へ送る操作は、同じ全関手圏で恒等を保つ。 -/
lemma dgModuleResolvedInfinity_isoOfRawFunctorIso_refl
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isoOfRawFunctorIso R C E F F (Iso.refl _) = Iso.refl _ := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_isoOfRawFunctorIso
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso]
  simp only [Functor.mapIso_refl]
  apply Iso.ext
  let r := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedInfinity_rawFactorIso R C E F
  change r.hom ≫ 𝟙 _ ≫ r.inv = 𝟙 _
  exact (congrArg (fun z => r.hom ≫ z) (Category.id_comp r.inv)).trans (Iso.hom_inv_id r)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
