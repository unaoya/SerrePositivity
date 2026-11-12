module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingStrictConeNative
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeArrowComp

/-!
概要：元指定 cone 入力同型の同じ逆を全厳密比較として保持する。
方針：既存の全 Hom 逆自然性と同じ実逆射を構成子へ渡す。
規約：元指定同型の逆を使用し、成分同値を選び直さない。
使われ方：元 gluing connecting 比較と全実逆回転の輸送。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma factoryArrow {R : Type u} [CommRing R] {C : Type v}
    [DGCategory R C] [Small.{u} C] {P : Type w} [DGCategory R P]
    (F G : DGFunctor R P (RightModule R C))
    (q : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
      ForgetEnrichment.of (Complex R) (G.obj x))
    (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (q y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (q x)
        (ForgetEnrichment.of (Complex R) (G.obj y))) (x : P) :
    dgModuleNaturalConeArrow R C F G
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R C (F := F) (G := G) q h) x = q x := by
  change (closedHomEquiv R (RightModule R C) _ _).symm
    ((closedHomEquiv R (RightModule R C) _ _) (q x)) = _
  exact (closedHomEquiv R (RightModule R C) _ _).symm_apply_apply _
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P : Type w} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "A" => dgIdentityHomGluingStrictConeFamily R C F G a h
local notation "B" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "e" => dgIdentityHomGluingStrictConeTypedInputIso R C F G a h

/-- 概要：元指定 cone 入力同型の同じ閉逆射。
方針：元実同型の逆射を取る。規約：元逆射を保持。
使われ方：全厳密逆比較の成分族。 -/
def dgIdentityHomGluingStrictConeInputInvMap (x : P) :
    ForgetEnrichment.of (Complex R) ((B).obj x) ⟶
      ForgetEnrichment.of (Complex R) ((A).obj x) := (e x).inv

/-- 概要：元指定入力逆射は全 Hom 鎖写像について自然。
方針：元全入力同型の全 Hom 自然性に既存の逆比較則を適用する。
規約：元指定逆射を保持。使われ方：全厳密逆比較の構成。 -/
lemma dgIdentityHomGluingStrictConeInputInvMap_naturality (x y : P) :
    (B).map x y ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) ((B).obj x))
      (dgIdentityHomGluingStrictConeInputInvMap R C F G a h y) =
    (A).map x y ≫ eHomWhiskerRight (Complex R)
      (dgIdentityHomGluingStrictConeInputInvMap R C F G a h x)
      (ForgetEnrichment.of (Complex R) ((A).obj y)) :=
  dgFunctorClosedComparison_inv_naturality R (A) (B) (e)
    (dgIdentityHomGluingStrictConeInputMap_naturality R C F G a h) x y

/-- 概要：元指定 cone 入力同型の同じ全厳密逆比較。
方針：元実逆射と全 Hom 自然性を既存構成子へ渡す。
規約：元逆射の全作用を保持。使われ方：元 gluing connecting の輸送。 -/
def dgIdentityHomGluingStrictConeInputInvComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (B) (A) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleStrictNatTransOfHomNaturality R C (F := (B)) (G := (A))
    (dgIdentityHomGluingStrictConeInputInvMap R C F G a h)
    (dgIdentityHomGluingStrictConeInputInvMap_naturality R C F G a h)

/-- 概要：全厳密入力逆比較の閉成分は元指定入力同型の逆射。
方針：既存構成子の閉射を回収する。
規約：元実逆射不変。使われ方：元 connecting 射の厳密回収。 -/
lemma dgIdentityHomGluingStrictConeInputInvComparison_arrow (x : P) :
    dgModuleNaturalConeArrow R C (B) (A)
      (dgIdentityHomGluingStrictConeInputInvComparison R C F G a h) x =
      dgIdentityHomGluingStrictConeInputInvMap R C F G a h x :=
  factoryArrow (R := R) (C := C) (B) (A)
    (dgIdentityHomGluingStrictConeInputInvMap R C F G a h)
    (dgIdentityHomGluingStrictConeInputInvMap_naturality R C F G a h) x
end SerrePositivity.KST.SConstruction
