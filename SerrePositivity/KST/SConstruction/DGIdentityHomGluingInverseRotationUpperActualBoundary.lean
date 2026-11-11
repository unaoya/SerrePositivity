module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationUpperNative
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeInrTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransNerveHomTransport
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomotopyInputExchange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomotopyRawTransport

/-!
概要：元実 connecting cone の包含を元指定逆回転全比較・元上二単体へ接続する。
方針：元入力等号を同じ包含と同じ指定全同型へ移送する。
規約：元包含・元全同型・負符号付き長辺を変更しない。
使われ方：元実始域上の全評価比較から元上指定二単体への合成。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma inclusionLawOfMiddleRecovery
    {A X : SSet.{u}} [SSet.Quasicategory X] {f g g' h : A ⟶ X}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (a' : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g')
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g' h) (b : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f h)
    (hg : g = g') (ha : HEq a a') (he : HEq e e') (hb : a' ≫ e'.hom = b) :
    a ≫ e.hom = b := by
  have hh := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorIso_hom_heq e e' hg rfl he
  have hc := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHom_comp_heq a e.hom a' e'.hom rfl hg rfl ha hh
  exact eq_of_heq (hc.trans (heq_of_eq hb))

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

local notation "MI" => dgIdentityHomGluingInverseRotationModuleSource R C F G a h
local notation "AI" => dgModuleNaturalConeInr R C (BS) (FSS) (βs)

/-- 概要：元実 connecting cone 包含は元生上二単体の同じ包含。
方針：元指定厳密逆の入力合成等号を元包含へ運ぶ。
規約：全厳密比較の型付き一致。使われ方：元実始域と元上二単体の境界照合。 -/
lemma dgIdentityHomGluingInverseRotationActualInr_heq : HEq (AI) (ι) :=
  dgModuleNaturalConeInr_heq R C (BS) (FSS) (βs) (BS) (FSS) (γs) rfl rfl
    (heq_of_eq (dgIdentityHomGluingInverseRotationStrict_input R C F G a h).symm)

/-- 概要：元実始域の全指定逆回転比較は元包含を元上二単体の指定長辺へ移す。
方針：元実包含と元生全比較を同じ端点回収で合成する。
規約：同じ元負符号付き長辺を保持。使われ方：元全実評価と元上二単体の接続。 -/
lemma dgIdentityHomGluingInverseRotationStrictNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (AI) ≫
      (dgIdentityHomGluingInverseRotationStrictNerveComparison R C F G a h).hom =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (λ) := by
  exact inclusionLawOfMiddleRecovery
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (AI))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (ι))
    (dgIdentityHomGluingInverseRotationStrictNerveComparison R C F G a h)
    (dgIdentityHomGluingInverseRotationUpperRawNerveComparison R C F G a h)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (λ))
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingInverseRotationStrict_source R C F G a h)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_heq R P (RightModule R C) (AI) (ι) rfl
      (dgIdentityHomGluingInverseRotationStrict_source R C F G a h).symm
      (dgIdentityHomGluingInverseRotationActualInr_heq R C F G a h))
    (dgIdentityHomGluingInverseRotationStrictNerveComparison_heq R C F G a h)
    (dgIdentityHomGluingInverseRotationUpperRawNerveComparison_inr R C F G a h)
end SerrePositivity.KST.SConstruction
