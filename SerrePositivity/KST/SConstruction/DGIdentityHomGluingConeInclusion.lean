module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingStrictConeNative
public import SerrePositivity.KST.SConstruction.DGModuleConeInputIsoBoundary
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeArrowComp
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInv
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConeConnectingNativeTriangle
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransNerveHom

/-!
概要：元実 gluing cone の右包含を元入力全同型・元上二単体と同時に保持する。
方針：元の自然 cone 包含を同じ指定入力同型で運び、元実包含そのものへ回収する。
規約：対象別の辺の選び直しをせず元全 Hom・元入力等号を保持する。
使われ方：元上指定二単体を同じ二段 realization へ接続する。
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
local notation "A" => dgIdentityHomGluingStrictConeFamily R C F G a h
local notation "B" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "e" => dgIdentityHomGluingStrictConeTypedInputIso R C F G a h
local notation "θ" => dgIdentityHomGluingStrictConeInputComparison R C F G a h

local notation "Y" => dgYoneda R C
local notation "FY" => F.comp (Y)
local notation "GY" => G.comp (Y)
local notation "η" => dgIdentityHomGluingYonedaStrictComparison R C F G a h
local notation "ι" => dgModuleNaturalConeInr R C (FY) (GY) (η)
local notation "I" => DGFunctor.id C
local notation "H" => dgIdentityHomGluingFunctor R C F G a h

/-- 概要：元実 gluing cone の同じ右包含を全厳密比較として保持する。
方針：元自然 cone 包含に元指定入力同型を後合成する。
規約：元入力同型・全 Hom を保持。使われ方：元実 cone の上二単体境界。 -/
def dgIdentityHomGluingModuleConeInr : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (GY) (B) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (ι) (θ)

/-- 概要：元実 cone 右包含の閉成分は元の実 moduleConeInr そのもの。
方針：元全合成の閉射と同じ cone 入力同型の包含回収を合成する。
規約：閉射の厳密等号。使われ方：元実 cone 包含の評価照合。 -/
lemma dgIdentityHomGluingModuleConeInr_arrow (x : P) :
    dgModuleNaturalConeArrow R C (GY) (B)
      (dgIdentityHomGluingModuleConeInr R C F G a h) x =
      moduleConeInr R C (dgHomGluingTargetModuleMap R C C C (I) (I) ((H).obj x)) := by
  change dgModuleNaturalConeArrow R C (GY) (B) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (ι) (θ)) x = _
  exact (dgModuleNaturalConeArrow_comp R C (GY) (A) (B) (ι) (θ) x).trans
    ((congrArg₂ (fun p q => p ≫ q)
      (dgModuleNaturalConeInr_arrow R C (FY) (GY) (η) x)
      (dgIdentityHomGluingStrictConeInputComparison_arrow R C F G a h x)).trans
        (dgModuleConeInputIso_inr R C _ _
          ((dgIdentityHomGluingYonedaStrictComparison_arrow R C F G a h x).trans
            (dgIdentityHomGluingTargetModuleMap R C F G a h x).symm)))

/-- 概要：元指定入力全同型は元自然 cone 包含を元実 cone 包含へ移す。
方針：同じ元全厳密合成を native 合成則へ写す。
規約：同じ指定全比較の順射。使われ方：元上二単体の native 境界。 -/
lemma dgIdentityHomGluingStrictConeInputNerveComparison_inr :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (ι) ≫
      (dgIdentityHomGluingStrictConeInputNerveComparison R C F G a h).hom =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C)
          (dgIdentityHomGluingModuleConeInr R C F G a h) := by
  exact (congrArg (fun m => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (ι) ≫ m)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_spec R P (RightModule R C) (θ)).symm).trans
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_comp R P (RightModule R C) (ι) (θ)).symm

/-- 概要：同じ入力全同型の逆は元実包含を元自然 cone 包含へ戻す。
方針：元順方向包含等号に同じ逆射を後合成する。
規約：元指定逆を保持。使われ方：元実 realization の入力境界。 -/
lemma dgIdentityHomGluingStrictConeInputNerveComparison_inr_inv :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C)
        (dgIdentityHomGluingModuleConeInr R C F G a h) ≫
      (dgIdentityHomGluingStrictConeInputNerveComparison R C F G a h).inv =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (ι) := by
  let nativeIso := dgIdentityHomGluingStrictConeInputNerveComparison R C F G a h
  let n := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R P (RightModule R C) (ι)
  exact (congrArg (fun t => t ≫ nativeIso.inv)
    (dgIdentityHomGluingStrictConeInputNerveComparison_inr R C F G a h)).symm.trans
      ((Category.assoc n nativeIso.hom nativeIso.inv).trans
        ((congrArg (fun t => n ≫ t) nativeIso.hom_inv_id).trans (Category.comp_id n)))

/-- 概要：元自然包含・元指定入力同型・元実包含の三辺を持つ実二単体。
方針：同じ全厳密合成等号を元三辺の全二単体へ束ねる。
規約：辺を類で置き換えない。使われ方：元上二単体の実入力移送。 -/
def dgIdentityHomGluingModuleConeInrTriangle :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (ι).homotopy (θ).homotopy
      (dgIdentityHomGluingModuleConeInr R C F G a h).homotopy :=
  Classical.choice (dgModuleStrictCompositionTriangle_nonempty
    (R := R) (C := C) (GY) (A) (B) (ι) (θ)
      (dgIdentityHomGluingModuleConeInr R C F G a h) rfl)
end SerrePositivity.KST.SConstruction
