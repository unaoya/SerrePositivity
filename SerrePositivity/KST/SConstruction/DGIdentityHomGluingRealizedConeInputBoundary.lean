module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingRealizedConeNativeBoundary
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConeInclusion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGStrictNerveWhiskerHom
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.SimplicialFunctors.FunctorHomotopyInputExchange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.FunctorHomTypedWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorTrianglePostcomposition

/-!
概要：元実 gluing cone の入力同型と実評価の全比較を、元右包含を保って接続する。
方針：元入力逆の包含則を同じ実評価で写し、元 cone 評価の包含則と合成する。
規約：元実包含・元指定逆・同じ元評価を保持する。
使われ方：元上指定二単体の二段 realization と固定 ν の接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  (J : DGFunctor R C (PerfectDGModule R E))
  {P : Type (max (u + 1) v)} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "Y" => dgYoneda R C
local notation "V" => dgPerfectRealization R C E J
local notation "K" => dgPerfectModuleUnderlying R E J
local notation "F0" => DGFunctor.comp (F.comp (Y)) (V)
local notation "G0" => DGFunctor.comp (G.comp (Y)) (V)
local notation "F1" => DGFunctor.comp F (K)
local notation "G1" => DGFunctor.comp G (K)
local notation "ηY" => dgIdentityHomGluingYonedaStrictComparison R C F G a h
local notation "η0" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ηY) (V)
local notation "εF" => dgPerfectRealizationYonedaRestrictedStrictComparison R E C J F
local notation "εG" => dgPerfectRealizationYonedaRestrictedStrictComparison R E C J G


local notation "η1" => dgIdentityHomGluingRealizedModuleComparison R E C J F G a h
local notation "CY" => dgIdentityHomGluingStrictConeFamily R C F G a h
local notation "CB" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "CT" => dgModuleNaturalConeFunctor R E (F1) (G1) (η1)

local notation "GY" => G.comp (Y)
local notation "ιA" => dgModuleNaturalConeInr R C (F.comp (Y)) (GY) (ηY)
local notation "ιB" => dgIdentityHomGluingModuleConeInr R C F G a h

/-- 概要：元入力同型が包含を運ぶ同じ全二単体の実 realization 像。
方針：元の全二単体を同じ tensor 評価でそのまま後合成する。
規約：三辺だけから別の二単体を選ばない。
使われ方：元指定上二単体を元実 cone 入力の前後で接続する。 -/
def dgIdentityHomGluingRealizedConeInputTriangle :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (ιA).homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V)))
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp
        (dgIdentityHomGluingStrictConeInputComparison R C F G a h).homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V)))
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (ιB).homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.postcomposeFunctorCompositionTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))
    (dgIdentityHomGluingModuleConeInrTriangle R C F G a h)

/-- 概要：元実入力二単体の realization は元の全図式の同じ後合成。
方針：元指定二単体の後合成定義を回収する。
規約：全二単体を保持。使われ方：元上二単体の prism 接続。 -/
lemma dgIdentityHomGluingRealizedConeInputTriangle_diagram :
    (dgIdentityHomGluingRealizedConeInputTriangle R E C J F G a h).diagram =
      (dgIdentityHomGluingModuleConeInrTriangle R C F G a h).diagram ≫
        (CategoryTheory.ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P)).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V)) := rfl

/-- 概要：元実 cone 入力の全逆比較は同じ元右包含の実評価像を保つ。
方針：元 native 包含等号を後合成し、同じ全厳密後合成との端点一致を使う。
規約：元包含・元逆比較の同じ射。使われ方：元評価全比較の入力側境界。 -/
lemma dgIdentityHomGluingRealizedConeInputNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ιB) (V)) ≫
      (dgIdentityHomGluingRealizedConeInputNerveComparison R E C J F G a h).hom =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ιA) (V)) := by
  let postMap := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V)
  let sourceInr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (ιB)
  let targetInr := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (ιA)
  let nativeIso := dgIdentityHomGluingStrictConeInputNerveComparison R C F G a h
  let rawIso := (nativeIso.postcomp postMap).symm
  have hraw : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (GY)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CB)) postMap sourceInr ≫
      rawIso.hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (GY)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CY)) postMap targetInr := by
    have hm := congrArg
      (fun t => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (GY)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CY)) postMap t)
      (dgIdentityHomGluingStrictConeInputNerveComparison_inr_inv R C F G a h)
    have hx : rawIso.hom =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CB)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CY)) postMap nativeIso.inv :=
      (congrArg (fun z => z.hom) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_symm nativeIso postMap)).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_postcomp_hom_typed nativeIso.symm postMap)
    exact (congrArg (fun t =>
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (GY)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CB)) postMap sourceInr ≫ t) hx).trans
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (GY)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CB)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CY))
          postMap sourceInr nativeIso.inv).symm.trans hm)
  have hi := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_postcomp_heq R P (RightModule R C)
    (RightModule R E) (ιB) (V)
  have ht := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_postcomp_heq R P (RightModule R C)
    (RightModule R E) (ιA) (V)
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq
    (dgIdentityHomGluingRealizedConeInputNerveComparison R E C J F G a h) rawIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (CB) (V)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (CY) (V))
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq rawIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (CB) (V)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (CY) (V)).symm)
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_comp_heq
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ιB) (V)))
    (dgIdentityHomGluingRealizedConeInputNerveComparison R E C J F G a h).hom
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (GY)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CB)) postMap sourceInr) rawIso.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (GY) (V)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (CB) (V)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (CY) (V)) hi he
  exact eq_of_heq (hc.trans ((heq_of_eq hraw).trans ht.symm))

/-- 概要：元実 gluing cone 全評価比較は元右包含の実像と厳密に可換。
方針：元入力逆と元評価 square の同じ包含回収を合成する。
規約：元実包含・元代表評価射を保持。使われ方：元上指定二単体の実評価境界。 -/
lemma dgIdentityHomGluingRealizedConeNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ιB) (V)) ≫
      (dgIdentityHomGluingRealizedConeNerveComparison R E C J F G a h).hom =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) (εG) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E)
            (dgModuleNaturalConeInr R E (F1) (G1) (η1)) := by
  let ni := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R E) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (ιB) (V))
  let inputIso := dgIdentityHomGluingRealizedConeInputNerveComparison R E C J F G a h
  let coneIso := dgIdentityHomGluingRealizedStrictConeNerveComparison R E C J F G a h
  change ni ≫ (inputIso.hom ≫ coneIso.hom) = _
  exact (Category.assoc ni inputIso.hom coneIso.hom).symm.trans
    ((congrArg (fun t => t ≫ coneIso.hom)
      (dgIdentityHomGluingRealizedConeInputNerveComparison_inr R E C J F G a h)).trans
        (dgIdentityHomGluingRealizedStrictConeNerveComparison_inr R E C J F G a h))
end SerrePositivity.KST.SConstruction
