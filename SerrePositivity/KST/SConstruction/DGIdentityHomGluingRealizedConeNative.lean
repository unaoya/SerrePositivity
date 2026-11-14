module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingRealizedComparison
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeImageNative
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeSquareNative
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingStrictConeNative
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：元実 gluing cone の realization を元実像射の cone へ全比較する。
方針：同じ元 cone image 比較と元二軸の指定評価 square を合成する。
規約：元全 Hom・元評価同型・元 cone 入力を保持する。
使われ方：元実逆回転 cone と指定上二単体を固定 ν へ接続する評価因子。
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

/-- 概要：元制限代表評価の閉成分は K(E) 同値。
方針：元指定代表評価同型を同じ K(E) 関手で写す。
規約：元閉成分を保持。使われ方：同じ元二軸評価の cone square 可逆性。 -/
lemma dgPerfectRealizationYonedaRestrictedComponent_isIso (x : P) :
    IsIso ((moduleToHomotopy R E).map
      (dgModuleNaturalConeArrow R E (F0) (F1) (εF) x)) := by
  rw [dgPerfectRealizationYonedaRestrictedStrictComparison_arrow]
  change IsIso ((moduleToHomotopy R E).map
    (dgPerfectRealizationRepresentableIso R C E J (F.obj x)).hom)
  exact (moduleToHomotopy R E).map_isIso _

/-- 概要：元自然 cone の realization から元実像射の cone への指定全比較。
方針：元 cone image の全比較の逆と元評価 square の全比較を合成する。
規約：元二軸評価・元全比較を保持。
使われ方：元実 gluing cone の全 realization 比較の中央因子。 -/
def dgIdentityHomGluingRealizedStrictConeNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((CY).comp (V))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CT)) := by
  exact (dgModuleNaturalConeImageNerveComparison R E C (F.comp (Y)) (G.comp (Y))
    (ηY) (V)).symm.trans
      (dgModuleNaturalConeSquareNerveComparison R E (F0) (G0) (F1) (G1)
        (η0) (η1) (εF) (εG) (dgIdentityHomGluingRealizedModuleSquare R E C J F G a h)
        (dgPerfectRealizationYonedaRestrictedComponent_isIso R E C J F) (dgPerfectRealizationYonedaRestrictedComponent_isIso R E C J G))

/-- 概要：元実 gluing cone 入力の realization を同じ自然 cone へ全比較する。
方針：元指定全入力同型を同じ実 realization で後合成する。
規約：元実 cone 入力の同じ全比較を保持。
使われ方：元実 gluing cone 族を元像射の cone へ接続する第一因子。 -/
def dgIdentityHomGluingRealizedConeInputNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((CB).comp (V))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((CY).comp (V))) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (((dgIdentityHomGluingStrictConeInputNerveComparison R C F G a h).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (V))).symm)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (CB) (V)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (CY) (V)).symm

/-- 概要：元実 gluing cone の realization と元実像射の cone の同じ全比較。
方針：元実入力全比較・元 cone image 全比較・指定評価 square 全比較を合成。
規約：対象別存在同値で元全比較を置き換えない。
使われ方：元実逆回転後の全比較と指定上下二単体の固定 ν 接続。 -/
def dgIdentityHomGluingRealizedConeNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((CB).comp (V))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CT)) :=
  (dgIdentityHomGluingRealizedConeInputNerveComparison R E C J F G a h).trans
    (dgIdentityHomGluingRealizedStrictConeNerveComparison R E C J F G a h)
end SerrePositivity.KST.SConstruction
