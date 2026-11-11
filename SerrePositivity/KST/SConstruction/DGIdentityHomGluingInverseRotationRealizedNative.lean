module
public import SerrePositivity.KST.SConstruction.DGIdentityInverseRotationModuleAxes
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingShiftedLeftAxis
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationRestrictedInput
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationModuleInput
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConePrecomp
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransTransport

/-!
概要：元実逆回転全比較と実 cone 全入力を元始域へ回収する。
方針：元全軸等号を前合成し同じ全 cone・shift 族へ接続する。
規約：元始域・元全 Hom・指定 shift を保持する。
使われ方：元実 gluing cone 全 realization 比較と同じ全実逆回転比較の接続。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  {P : Type (max (u + 1) v)} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "I" => DGFunctor.id C
local notation "M" => dgHomGluingBimodule R C C C (I) (I)
local notation "H" => dgIdentityHomGluingFunctor R C F G a h

local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C C (M)
local notation "family" => dgHomGluingLoopConeFamily R C C C (I) (I)
local notation "J" => dgSmallPerfectEnvelopeInclusion R C ((L) ⊕ (L)) (family)
local notation "K" => dgPerfectModuleUnderlying R C (J)
local notation "Loop" => dgHomGluingLoopConeSmall R C C C (I) (I)
local notation "DS" => dgHomGluingLoopConeShiftedTarget R C C C (I) (I)
local notation "B" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "FS" => DGFunctor.comp (F.comp (dgYoneda R C)) (moduleShiftDG R C 1)
local notation "S" => moduleShiftDG R C (-1)

local notation "η" => dgIdentityInverseRotationImageComparison R C
local notation "β" => dgIdentityHomGluingConeConnectingComparison R C F G a h
local notation "βs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (β) (S)

/-- 概要：元実逆回転 gluing cone の全 realization を元始域の同じ実 cone へ比較。
方針：元全比較を前合成し、同じ全入力回収だけで端点を輸送する。
規約：元全 Hom と元始域を保持。使われ方：指定厳密逆による全合成比較の第一因子。 -/
def dgIdentityHomGluingInverseRotationRealizedInputNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((H).comp (dgIdentityInverseRotationRealizedConeFamily R C)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingInverseRotationModuleSource R C F G a h)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    ((dgIdentityInverseRotationRealizedConeNerveComparison R C).precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (H)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (H) (dgIdentityInverseRotationRealizedConeFamily R C)).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (H) (dgIdentityInverseRotationImageConeFamily R C)).symm.trans
      (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        (dgIdentityHomGluingInverseRotationImageConeFamily_restriction R C F G a h)))

/-- 概要：元実逆回転 gluing cone の全 realization と元第二 Yoneda 族の全比較。
方針：同じ実像 cone の全比較と元指定厳密逆の三因子比較を合成する。
規約：元始域・元実逆回転・指定厳密逆を保持。
使われ方：LT 実右面の合成全比較と固定 ν の上下指定二単体への接続。 -/
def dgIdentityHomGluingInverseRotationRealizedNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((H).comp (dgIdentityInverseRotationRealizedConeFamily R C)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (G.comp (dgYoneda R C))) :=
  (dgIdentityHomGluingInverseRotationRealizedInputNerveComparison R C F G a h).trans
    (dgIdentityHomGluingInverseRotationStrictNerveComparison R C F G a h)
end SerrePositivity.KST.SConstruction
