module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingStrictConeInverse
public import SerrePositivity.KST.SConstruction.DGModuleConeInputIsoBoundary

/-!
概要：元始域上の同じ gluing cone の connecting 射を全厳密比較として保持する。
方針：元入力同型の全厳密逆と元全 connecting 比較を合成し同じ実成分を回収する。
規約：元実射・全 Hom 作用を保持する。
使われ方：同じ指定入力比較を connecting・逆 shift へ接続する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P : Type w} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "J" => dgYoneda R C
local notation "I" => DGFunctor.id C
local notation "H" => dgIdentityHomGluingFunctor R C F G a h
local notation "B" => dgIdentityHomGluingModuleConeFamily R C F G a h
local notation "FS" => DGFunctor.comp (F.comp (J)) (moduleShiftDG R C 1)
local notation "d" => dgHomGluingTargetModuleMap R C C C (I) (I)

/-- 概要：元始域上の同じ実 gluing cone の connecting 射。
方針：始終の全関手族の型を明示する。
規約：元実射を保持。使われ方：同じ指定 connecting 全比較の閉成分。 -/
def dgIdentityHomGluingConeConnectingMap (x : P) :
    ForgetEnrichment.of (Complex R) ((B).obj x) ⟶
      ForgetEnrichment.of (Complex R) ((FS).obj x) :=
  moduleConeConnecting R C (d ((H).obj x))

/-- 概要：元 gluing cone の同じ connecting を持つ全厳密比較。
方針：同じ元入力同型の全厳密逆と元全 connecting 比較を合成する。
規約：元指定実同型と全 Hom 作用を保持する。
使われ方：同じ指定入力比較を connecting・逆 shift に接続する。 -/
def dgIdentityHomGluingConeConnectingComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans (B) (FS) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransComp (dgIdentityHomGluingStrictConeInputInvComparison R C F G a h)
    (dgModuleNaturalConeConnecting R C (F.comp (J)) (G.comp (J))
      (dgIdentityHomGluingYonedaStrictComparison R C F G a h))
end SerrePositivity.KST.SConstruction
