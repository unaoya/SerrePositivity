module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationUpperComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransNerveHom
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConePrecompositionBoundary
public import SerrePositivity.KST.SConstruction.DGModuleNaturalInverseRotationRestriction
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConeConnectingNativeTriangle

/-!
概要：元指定厳密逆の native 全比較に元包含・指定上二単体の同じ辺を保持する。
方針：native 全比較の順射を元全厳密比較の nerve 射へ厳密回収する。
規約：元実上二単体を別の同型や別の辺代表で置換しない。
使われ方：実 realization の全比較へ元包含・負符号・指定上二単体を接続する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P : Type (max (u + 1) v)} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "J" => dgYoneda R C
local notation "A" => dgIdentityHomGluingStrictConeFamily R C F G a h
local notation "B" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "FS" => DGFunctor.comp (F.comp (J)) (moduleShiftDG R C 1)
local notation "S" => moduleShiftDG R C (-1)
local notation "η" => dgIdentityHomGluingYonedaStrictComparison R C F G a h
local notation "δ" => dgModuleNaturalConeConnecting R C (F.comp (J)) (G.comp (J)) (η)
local notation "α" => dgIdentityHomGluingStrictConeInputComparison R C F G a h
local notation "β" => dgIdentityHomGluingConeConnectingComparison R C F G a h
local notation "αs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (α) (S)
local notation "βs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (β) (S)
local notation "δs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (δ) (S)


local notation "κ" => dgIdentityHomGluingStrictConeInputInvComparison R C F G a h
local notation "κs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (κ) (S)


local notation "GY" => G.comp (J)
local notation "FY" => F.comp (J)
local notation "AS" => DGFunctor.comp (A) (S)
local notation "BS" => DGFunctor.comp (B) (S)
local notation "FSS" => DGFunctor.comp (FS) (S)
local notation "γs" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (κs) (δs)
local notation "RS" => dgModuleNaturalConeFunctor R C (BS) (FSS) (γs)
local notation "NS" => dgModuleNaturalInverseRotationSource R C (FY) (GY) (η)
local notation "q" => dgModuleNaturalConePrecomposition R C (BS) (AS) (FSS) (κs) (δs)
local notation "σ" => dgModuleNaturalInverseRotation R C (FY) (GY) (η)
local notation "ι" => dgModuleNaturalConeInr R C (BS) (FSS) (γs)
local notation "ιn" => dgModuleNaturalConeInr R C (AS) (FSS) (δs)
local notation "λ" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (ιn) (σ)

local notation "ρ" => dgIdentityHomGluingInverseRotationUpperRawComparison R C F G a h

/-- 概要：元指定厳密逆と元実三因子による同じ生の native 全関手同型。
方針：元 cone 前合成と元全実逆回転を元順序で合成する。
規約：新しい逆や成分同値を選ばない。使われ方：元上二単体の指定後辺の回収。 -/
def dgIdentityHomGluingInverseRotationUpperRawNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (RS)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (GY)) :=
  (dgModuleNaturalConePrecompositionNerveComparison R C (BS) (AS) (FSS) (κs) (δs)
    (dgIdentityHomGluingInverseRotationStrictInput_isIso R C F G a h)).trans
      (dgModuleNaturalInverseRotationNerveComparison R C (FY) (GY) (η))

/-- 概要：元生 native 全比較の順射は元上二単体の同じ後辺の nerve 射。
方針：元二因子の順射と厳密変換の native 合成則を回収する。
規約：元全辺を保持。使われ方：元包含三角形の native 全比較への接続。 -/
lemma dgIdentityHomGluingInverseRotationUpperRawNerveComparison_hom :
    (dgIdentityHomGluingInverseRotationUpperRawNerveComparison R C F G a h).hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (ρ) := by
  change SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (q).homotopy) ≫
    SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (σ).homotopy) = _
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_homotopyHom_comp R P (RightModule R C) (q) (σ)).symm.trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_spec R P (RightModule R C) (ρ)).symm

/-- 概要：元包含と生 native 全比較の合成は元指定長辺の同じ native 射。
方針：元全厳密包含等号と native 順射回収を合成する。
規約：元指定長辺・負符号を保持。使われ方：指定上二単体の境界認証。 -/
lemma dgIdentityHomGluingInverseRotationUpperRawNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (ι) ≫
      (dgIdentityHomGluingInverseRotationUpperRawNerveComparison R C F G a h).hom =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (λ) := by
  rw [dgIdentityHomGluingInverseRotationUpperRawNerveComparison_hom]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_comp R P (RightModule R C) (ι) (ρ)).symm.trans
    (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) t)
      (dgIdentityHomGluingInverseRotationUpperRawComparison_inr R C F G a h))

/-- 概要：元実始域の指定 native 全比較は元上二単体の生比較の端点回収そのもの。
方針：元指定厳密逆の構成を回収する。
規約：比較値・元辺代表を変更しない。使われ方：元上二単体と実全比較の同時輸送。 -/
lemma dgIdentityHomGluingInverseRotationStrictNerveComparison_upper :
    dgIdentityHomGluingInverseRotationStrictNerveComparison R C F G a h =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (dgIdentityHomGluingInverseRotationUpperRawNerveComparison R C F G a h)
        (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingInverseRotationStrict_source R C F G a h)) rfl := rfl
end SerrePositivity.KST.SConstruction
