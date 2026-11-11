module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingInverseRotationStrict
public import SerrePositivity.KST.SConstruction.DGHomGluingInverseRotationCone

/-!
概要：全実 connecting の逆 shift 閉射を元 gluing の同じ実逆回転射へ戻す。
方針：同じ全厳密比較の閉成分・元 shift 射の二回収を適用する。
規約：元の実 cone 入力を保持する。
使われ方：全実逆回転比較と元 gluing の実 cone の全関手照合。
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


local notation "I" => DGFunctor.id C
local notation "K" => dgIdentityHomGluingFunctor R C F G a h
local notation "L" => dgIdentityHomGluingInverseRotationModuleSource R C F G a h

/-- 概要：逆 shift 全実 connecting の閉成分は元 gluing の実逆回転射。
方針：元 shift 閉射・元 connecting 閉射の回収を合成する。
規約：元実射の厳密等式。使われ方：同じ実 cone 入力の照合。 -/
lemma dgIdentityHomGluingInverseRotationModuleArrow (x : P) :
    dgModuleNaturalConeArrow R C ((B).comp (S)) ((FS).comp (S)) (βs) x =
      dgHomGluingInverseRotationModuleMap R C C C (I) (I) ((K).obj x) := by
  exact (dgModuleNaturalConeShiftArrow R C (B) (FS) (β) (-1) x).trans
    ((congrArg (moduleShiftMap R C (-1))
      (dgIdentityHomGluingConeConnectingComparison_arrow R C F G a h x)).trans
        (dgHomGluingInverseRotationModuleMap_eq R C C C (I) (I) ((K).obj x)).symm)

/-- 概要：全実逆回転入力 cone と元 gluing 実逆回転 cone の指定同型。
方針：元入力射の厳密回収だけで実 cone を輸送する。
規約：対象別同値を選択しない。使われ方：元実比較射の成分照合。 -/
def dgIdentityHomGluingInverseRotationModuleInputIso (x : P) :
    ForgetEnrichment.of (Complex R) ((L).obj x) ≅
      moduleCone R C (dgHomGluingInverseRotationModuleMap R C C C (I) (I) ((K).obj x)) :=
  eqToIso (congrArg (fun f => moduleCone R C f)
    (dgIdentityHomGluingInverseRotationModuleArrow R C F G a h x))
end SerrePositivity.KST.SConstruction
