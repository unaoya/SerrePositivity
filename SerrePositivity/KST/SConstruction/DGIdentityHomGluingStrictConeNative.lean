module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingStrictConeNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleStrictNatTransIso

/-!
概要：元 gluing cone の指定入力全比較を native 全関手同型へ接続する。
方針：元全厳密比較の同じ閉成分が指定実同型であることを使う。
規約：元入力同型・全 Hom 作用を保持する。
使われ方：全実逆回転比較の元 gluing 始域輸送。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
open scoped Simplicial
private lemma recoverStrictArrow {R : Type u} [CommRing R]
    {C : Type v} [DGCategory R C] [Small.{u} C]
    {P : Type (max (u + 1) v)} [DGCategory R P]
    (F G : DGFunctor R P (RightModule R C)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
    (x : P) (q : ForgetEnrichment.of (Complex R) (F.obj x) ⟶
      ForgetEnrichment.of (Complex R) (G.obj x))
    (hc : η.app x = cycleFromUnit (moduleHom R C (F.obj x) (G.obj x))
      (ForgetEnrichment.homTo (Complex R) q)) :
    dgModuleNaturalConeArrow R C F G η x = q :=
  (congrArg (closedHomEquiv R (RightModule R C) _ _).symm hc).trans
    ((closedHomEquiv R (RightModule R C) _ _).symm_apply_apply q)
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

/-- 概要：元入力全比較の閉射は元指定入力同型の順射。
方針：閉射・閉元対応の逆律を使用。
規約：元同型を保持。使われ方：同じ全比較の指定成分回収。 -/
lemma dgIdentityHomGluingStrictConeInputComparison_arrow (x : P) :
    dgModuleNaturalConeArrow R C (A) (B) (θ) x =
      dgIdentityHomGluingStrictConeInputMap R C F G a h x :=
  recoverStrictArrow (R := R) (C := C) (P := P) (A) (B) (θ) x (dgIdentityHomGluingStrictConeInputMap R C F G a h x)
    (dgIdentityHomGluingStrictConeInputComparison_cycle R C F G a h x)

/-- 概要：元 cone 入力の同じ指定実同型を保持する native 全関手同型。
方針：元全ホモトピーと同じ実入力同型の可逆性を束ねる。
規約：点ごとの同値選択で全比較を代用しない。
使われ方：元厳密 gluing cone と全実逆回転比較の接続。 -/
def dgIdentityHomGluingStrictConeInputNerveComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (A)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (B)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorIsoOfStrictNatTrans R C (F := (A)) (G := (B)) (θ)
    (dgIdentityHomGluingStrictConeInputMap R C F G a h)
    (dgIdentityHomGluingStrictConeInputComparison_cycle R C F G a h)
    (fun x => (e x).isIso_hom)
end SerrePositivity.KST.SConstruction
