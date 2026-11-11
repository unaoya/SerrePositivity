module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationStrict
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConePrecompositionBoundary
public import SerrePositivity.KST.SConstruction.DGModuleNaturalInverseRotationRestriction
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConeConnectingNativeTriangle

/-!
概要：元指定入力逆の実逆回転全比較と包含合成二単体を保持する。
方針：元 cone 前合成が包含を保持する全厳密等号を使用する。
規約：元全実逆回転・元右包含・指定長辺を保持する。
使われ方：元実逆回転から固定 ν の指定上二単体への接続。
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

/-- 概要：元指定厳密逆による全実逆回転の生の厳密合成比較。
方針：同じ cone 前合成比較と元三因子の全比較を合成する。
規約：元全 Hom を保持。使われ方：包含を保つ実合成二単体。 -/
def dgIdentityHomGluingInverseRotationUpperRawComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (RS) (GY) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (q) (σ)
local notation "ρ" => dgIdentityHomGluingInverseRotationUpperRawComparison R C F G a h

/-- 概要：生の全逆回転比較の包含制限は元指定長辺そのもの。
方針：cone 前合成の全包含等号と全厳密合成の結合則を使用する。
規約：全厳密比較の等号。使われ方：元右包含を保つ実合成面。 -/
lemma dgIdentityHomGluingInverseRotationUpperRawComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (ι) (ρ) = (λ) := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp_assoc (ι) (q) (σ)).symm.trans
    (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp t (σ))
      (dgModuleNaturalConePrecomposition_inr R C (BS) (AS) (FSS) (κs) (δs)))

/-- 概要：元包含・全逆回転比較・指定長辺の三辺を持つ実二単体。
方針：全厳密合成等号を指定三辺の実合成三角形へ渡す。
規約：全三辺を辺の類へ弱めない。
使われ方：元実逆回転比較の指定包含面。 -/
def dgIdentityHomGluingInverseRotationUpperRawTriangle :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (ι).homotopy (ρ).homotopy (λ).homotopy := by
  exact Classical.choice (dgModuleStrictCompositionTriangle_nonempty
    (R := R) (C := C) (FSS) (RS) (GY) (ι) (ρ) (λ)
    (dgIdentityHomGluingInverseRotationUpperRawComparison_inr R C F G a h))

/-- 概要：生の全逆回転比較の包含制限は元比較の負符号を保持する。
方針：全包含等号の同じ閉射へ元全実逆回転の符号回収を適用。
規約：元実射と指定相殺を保持。使われ方：指定上二単体の元長辺照合。 -/
lemma dgIdentityHomGluingInverseRotationUpperRawComparison_inr_sign (x : P) :
    moduleConeInr R C (dgModuleNaturalConeArrow R C (BS) (FSS) (γs) x) ≫
      dgModuleNaturalConeArrow R C (RS) (GY) (ρ) x =
      moduleShiftMap R C (-1)
        (dgModuleNaturalInverseRotationSignedArrow R C (FY) (GY) (η) x) ≫
          Iso.hom (dgModuleSpecifiedCancellationIso R C ((GY).obj x)) := by
  have ht := congrArg (fun t => dgModuleNaturalConeArrow R C (FSS) (GY) t x)
    (dgIdentityHomGluingInverseRotationUpperRawComparison_inr R C F G a h)
  rw [dgModuleNaturalConeArrow_comp, dgModuleNaturalConeInr_arrow] at ht
  exact ht.trans ((dgModuleNaturalConeArrow_comp R C (FSS) (NS) (GY) (ιn) (σ) x).trans
    ((congrArg (fun t => t ≫ dgModuleNaturalConeArrow R C (NS) (GY) (σ) x)
      (dgModuleNaturalConeInr_arrow R C (AS) (FSS) (δs) x)).trans
        (dgModuleNaturalInverseRotation_inr_sign R C (FY) (GY) (η) x)))
end SerrePositivity.KST.SConstruction
