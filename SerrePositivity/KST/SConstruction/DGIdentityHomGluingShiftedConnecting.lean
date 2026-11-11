module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConnectingConeNative
public import SerrePositivity.KST.SConstruction.DGStrictCompositionPostcomp
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeShiftArrow
public import SerrePositivity.KST.SConstruction.DGModuleNaturalInverseRotationNative

/-!
概要：元 gluing の connecting 合成全比較を同じ逆 shift で保持する。
方針：全厳密合成等号と元閉成分の回収を実 dg shift へ写す。
規約：同じ三つの比較と同じ指定 shift を使用する。
使われ方：元実逆回転 cone の入力全比較。
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

/-- 概要：元入力比較と実 connecting の全合成等号は逆 shift 後も成立。
方針：元全厳密合成の後合成保存を使用する。
規約：同じ指定三辺。使われ方：実逆回転 cone の元長辺回収。 -/
lemma dgIdentityHomGluingShiftedConnecting_input :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (αs) (βs) = (δs) := by
  exact (dgStrictCompositionPostcomp (α) (β) (S)).trans
    (congrArg (fun t => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp t (S))
      (dgIdentityHomGluingConeConnectingComparison_input R C F G a h))

/-- 概要：元指定入力比較の逆 shift の閉成分は K(C) 同値。
方針：元実 shift 射を回収し dg shift の K(C) 関手で写す。
規約：元入力同型の shift を使用。使われ方：実逆回転入力 cone の可逆性。 -/
lemma dgIdentityHomGluingShiftedConnectingInput_isIso (x : P) :
    IsIso ((moduleToHomotopy R C).map
      (dgModuleNaturalConeArrow R C ((A).comp (S)) ((B).comp (S)) (αs) x)) := by
  rw [dgModuleNaturalConeShiftArrow, ← moduleShiftDG_map_eq]
  change IsIso ((S).onHomotopy.map ((moduleToHomotopy R C).map
    (dgModuleNaturalConeArrow R C (A) (B) (α) x)))
  haveI := dgIdentityHomGluingConnectingConeInput_isIso R C F G a h x
  infer_instance

/-- 概要：元実 connecting の逆 shift の同じ cone 族。
方針：同じ全実 connecting の逆 shift を元 cone 関手へ渡す。
規約：閉成分を任意選択しない。使われ方：元 gluing 実逆回転の加群側始域。 -/
def dgIdentityHomGluingInverseRotationModuleSource : DGFunctor R P (RightModule R C) :=
  dgModuleNaturalConeFunctor R C ((B).comp (S)) ((FS).comp (S)) (βs)

/-- 概要：逆 shift 後の全合成 cone は元全実逆回転の始域に一致。
方針：同じ全合成等号へ cone 関手を適用する。
規約：元全関手の等号。使われ方：元実逆回転入力比較の始域回収。 -/
lemma dgIdentityHomGluingShiftedConnectingCone_source :
    dgModuleNaturalConeFunctor R C ((A).comp (S)) ((FS).comp (S))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (αs) (βs)) =
        dgModuleNaturalInverseRotationSource R C (F.comp (J)) (G.comp (J)) (η) :=
  congrArg (dgModuleNaturalConeFunctor R C ((A).comp (S)) ((FS).comp (S)))
    (dgIdentityHomGluingShiftedConnecting_input R C F G a h)

/-- 概要：元全実逆回転始域から元実 connecting の逆 shift cone への全比較。
方針：指定入力比較の逆 shift に同じ cone 前合成比較を適用する。
規約：同じ全比較を端点等号だけで回収する。
使われ方：元 gluing の実逆回転射への全関手比較。 -/
def dgIdentityHomGluingInverseRotationInputNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgModuleNaturalInverseRotationSource R C (F.comp (J)) (G.comp (J)) (η)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingInverseRotationModuleSource R C F G a h)) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (dgModuleNaturalConePrecompositionNerveComparison R C ((A).comp (S)) ((B).comp (S))
      ((FS).comp (S)) (αs) (βs)
      (dgIdentityHomGluingShiftedConnectingInput_isIso R C F G a h))
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingShiftedConnectingCone_source R C F G a h)) rfl

/-- 概要：元実 connecting の逆 shift cone から元第二 Yoneda 族への全比較。
方針：同じ入力全比較の逆と元三因子の全実逆回転比較を合成する。
規約：全比較の元指定成分を保持する。
使われ方：元実 gluing 逆回転 cone と指定商合成の全比較。 -/
def dgIdentityHomGluingInverseRotationModuleNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgIdentityHomGluingInverseRotationModuleSource R C F G a h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (G.comp (J))) :=
  (dgIdentityHomGluingInverseRotationInputNerveComparison R C F G a h).symm.trans
    (dgModuleNaturalInverseRotationNerveComparison R C (F.comp (J)) (G.comp (J)) (η))
end SerrePositivity.KST.SConstruction
