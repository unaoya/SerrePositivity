module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingConeConnectingRecovery

/-!
概要：元 cone 入力比較と元実 connecting の全合成三角形を保つ。
方針：元指定入力同型の順逆成分を同じ全厳密比較の合成に適用する。
規約：全厳密自然変換の等号で指定長辺を回収する。
使われ方：元実逆回転・固定 ν の上二単体と全図式比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma isoTriangle {V : Type*} [Category V] {X Y Z : V} (e : X ≅ Y) (f : X ⟶ Z) :
    e.hom ≫ (e.inv ≫ f) = f := by
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
private lemma strictInputTriangle {R : Type u} [CommRing R] {C : Type v}
    [DGCategory R C] [Small.{u} C] {P : Type w} [DGCategory R P]
    (F G H : DGFunctor R P (RightModule R C))
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (κ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans G F) (δ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F H)
    (e : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ≅
      ForgetEnrichment.of (Complex R) (G.obj x))
    (hη : ∀ x, dgModuleNaturalConeArrow R C F G η x = (e x).hom)
    (hκ : ∀ x, dgModuleNaturalConeArrow R C G F κ x = (e x).inv) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp η (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp κ δ) = δ := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_ext
  intro x
  apply (closedHomEquiv R (RightModule R C) (F.obj x) (H.obj x)).symm.injective
  exact (dgModuleNaturalConeArrow_comp R C F G H η (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp κ δ) x).trans
    ((congrArg₂ (fun f g => f ≫ g) (hη x)
      ((dgModuleNaturalConeArrow_comp R C G F H κ δ x).trans
        (congrArg (fun f => f ≫ dgModuleNaturalConeArrow R C F H δ x) (hκ x)))).trans
          (isoTriangle (e x) (dgModuleNaturalConeArrow R C F H δ x)))
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
local notation "η" => dgIdentityHomGluingYonedaStrictComparison R C F G a h
local notation "δ" => dgModuleNaturalConeConnecting R C (F.comp (J)) (G.comp (J)) (η)
local notation "e" => dgIdentityHomGluingStrictConeTypedInputIso R C F G a h

/-- 概要：元入力比較と元実 connecting の全合成は元 connecting 全比較そのもの。
方針：同じ指定入力同型の全厳密順逆比較と元 connecting を合成する。
規約：成分等式だけに弱めず全厳密比較の等号を保持。
使われ方：指定合成二単体の長辺を元の全 connecting へ回収する。 -/
lemma dgIdentityHomGluingConeConnectingComparison_input :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (dgIdentityHomGluingStrictConeInputComparison R C F G a h)
      (dgIdentityHomGluingConeConnectingComparison R C F G a h) = (δ) :=
  strictInputTriangle (R := R) (C := C) (A) (B) (FS)
    (dgIdentityHomGluingStrictConeInputComparison R C F G a h)
    (dgIdentityHomGluingStrictConeInputInvComparison R C F G a h) (δ) (e)
    (dgIdentityHomGluingStrictConeInputComparison_arrow R C F G a h)
    (dgIdentityHomGluingStrictConeInputInvComparison_arrow R C F G a h)
end SerrePositivity.KST.SConstruction
