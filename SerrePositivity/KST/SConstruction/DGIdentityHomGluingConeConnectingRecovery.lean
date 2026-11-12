module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConeConnecting

/-!
概要：全厳密輸送した gluing connecting 比較を元実 connecting 射へ戻す。
方針：同じ元入力逆同型・元全 connecting の閉射を回収する。
規約：元入力同型の指定逆と同じ実 connecting 射を保持する。
使われ方：元実逆回転の指定 connecting 境界と合成二単体。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma compCongr {V : Type*} [Category V] {X Y Z : V}
    (a a' : X ⟶ Y) (b b' : Y ⟶ Z) (ha : a = a') (hb : b = b') :
    a ≫ b = a' ≫ b' := congrArg₂ (fun f g => f ≫ g) ha hb
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
private lemma inverseConnecting {M N : ModuleCategory R C}
    (f f' : M ⟶ N) (h : f = f') (e : moduleCone R C f ≅ moduleCone R C f')
    (he : e = eqToIso (congrArg (fun t => moduleCone R C t) h)) :
    e.inv ≫ moduleConeConnecting R C f = moduleConeConnecting R C f' := by
  have hc : moduleConeConnecting R C f = e.hom ≫ moduleConeConnecting R C f' := by
    rw [he]
    exact dgModuleConeInputIso_connecting R C f f' h
  exact (Iso.inv_comp_eq e).2 hc
variable {P : Type w} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "J" => dgYoneda R C
local notation "I" => DGFunctor.id C
local notation "H" => dgIdentityHomGluingFunctor R C F G a h
local notation "A" => dgIdentityHomGluingStrictConeFamily R C F G a h
local notation "B" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "FS" => DGFunctor.comp (F.comp (J)) (moduleShiftDG R C 1)
local notation "η" => dgIdentityHomGluingYonedaStrictComparison R C F G a h
local notation "δ" => dgModuleNaturalConeConnecting R C (F.comp (J)) (G.comp (J)) (η)
local notation "e" => dgIdentityHomGluingStrictConeTypedInputIso R C F G a h
local notation "c" => dgModuleNaturalConeArrow R C (F.comp (J)) (G.comp (J)) (η)
local notation "d" => dgHomGluingTargetModuleMap R C C C (I) (I)

/-- 概要：同じ全 gluing connecting 比較の閉射は元実 connecting 射そのもの。
方針：元指定入力逆・元 connecting の閉成分を同じ cone 入力等号で回収する。
規約：元実射不変。使われ方：全実逆回転の元指定成分と connecting 境界。 -/
lemma dgIdentityHomGluingConeConnectingComparison_arrow (x : P) :
    dgModuleNaturalConeArrow R C (B) (FS)
      (dgIdentityHomGluingConeConnectingComparison R C F G a h) x =
      dgIdentityHomGluingConeConnectingMap R C F G a h x :=
  (dgModuleNaturalConeArrow_comp R C (B) (A) (FS)
    (dgIdentityHomGluingStrictConeInputInvComparison R C F G a h) (δ) x).trans
    ((compCongr _ _ _ _
      (dgIdentityHomGluingStrictConeInputInvComparison_arrow R C F G a h x)
      (dgModuleNaturalConeConnecting_arrow R C (F.comp (J)) (G.comp (J)) (η) x)).trans
        (inverseConnecting R C (c x) (d ((H).obj x))
          ((dgIdentityHomGluingYonedaStrictComparison_arrow R C F G a h x).trans
            (dgIdentityHomGluingTargetModuleMap R C F G a h x).symm) (e x) rfl))
end SerrePositivity.KST.SConstruction
