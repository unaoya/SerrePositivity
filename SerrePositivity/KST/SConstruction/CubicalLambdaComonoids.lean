module
public import SerrePositivity.KST.SConstruction.CubicalLambda
public import SerrePositivity.KST.SConstruction.CubicalSerreDayComonoidMonoidal

/-! # Λ の元の Serre 余モノイド構造
概要：Λ の全 Hom・単位・合成と入力作用を、元の Serre 余モノイドの射へ持ち上げる。
方針：同じ余モノイド値強モノイダル関手の構造射を使い、元の underlying 射を回収する。
規約：元の Serre 対角と増大を保持。使われ方：Λ の oplax tensor の実 dg 関手。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Simplicial SSet
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の Λ の Hom 複体に持たせる Serre 余モノイド。 -/
def cubicalLambdaHomComonoid (K : SSet.{u}) (x y : CubicalLambda A K) :
    Comon (Complex A) :=
  (cubicalDaySerreComonoids A).obj (necklaceCubicalDayMapping K x y)

/-- 元の Hom 余モノイドは、同じ Hom 複体を underlying 対象とする。 -/
lemma cubicalLambdaHomComonoid_X (K : SSet.{u}) (x y : CubicalLambda A K) :
    (cubicalLambdaHomComonoid A K x y).X = (x ⟶[Complex A] y) := rfl

/-- 元の Λ の Hom 複体上の、元の Serre 対角・増大による余モノイド構造。 -/
instance cubicalLambdaHom_comon (K : SSet.{u}) (x y : CubicalLambda A K) :
    ComonObj (x ⟶[Complex A] y) :=
  (cubicalLambdaHomComonoid A K x y).comon

/-- Λ の元の単位射を、同じ余モノイドの射として読む。 -/
def cubicalLambdaIdentityComonoid (K : SSet.{u}) (x : CubicalLambda A K) :
    𝟙_ (Comon (Complex A)) ⟶ cubicalLambdaHomComonoid A K x x :=
  Functor.LaxMonoidal.ε (cubicalDaySerreComonoids A) ≫
    (cubicalDaySerreComonoids A).map (necklaceCubicalDayIdentity K x)

/-- 単位の余モノイド射は、元の Λ の単位を厳密に回収する。 -/
lemma cubicalLambdaIdentityComonoid_hom (K : SSet.{u}) (x : CubicalLambda A K) :
    (cubicalLambdaIdentityComonoid A K x).hom = eId (Complex A) x := rfl

/-- Λ の元の合成を、同じ Hom 余モノイドの tensor からの射として読む。 -/
def cubicalLambdaComposeComonoid (K : SSet.{u}) (x y z : CubicalLambda A K) :
    cubicalLambdaHomComonoid A K x y ⊗ cubicalLambdaHomComonoid A K y z ⟶
      cubicalLambdaHomComonoid A K x z :=
  Functor.LaxMonoidal.μ (cubicalDaySerreComonoids A)
      (necklaceCubicalDayMapping K x y) (necklaceCubicalDayMapping K y z) ≫
    (cubicalDaySerreComonoids A).map (necklaceCubicalDayCompose K x y z)

/-- 合成の余モノイド射は、元の Λ の合成を厳密に回収する。 -/
lemma cubicalLambdaComposeComonoid_hom (K : SSet.{u}) (x y z : CubicalLambda A K) :
    (cubicalLambdaComposeComonoid A K x y z).hom = eComp (Complex A) x y z := rfl

/-- 元の全入力写像の Hom 作用を、同じ Serre 余モノイドの射として読む。 -/
def cubicalLambdaMapComonoid {K L : SSet.{u}} (a : K ⟶ L) (x y : CubicalLambda A K) :
    cubicalLambdaHomComonoid A K x y ⟶
      cubicalLambdaHomComonoid A L ((cubicalLambdaMap A a).obj x)
        ((cubicalLambdaMap A a).obj y) :=
  (cubicalDaySerreComonoids A).map (.mk (necklaceCubicalMap a x y))

/-- 入力の余モノイド射は、元の Λ の Hom 作用を厳密に回収する。 -/
lemma cubicalLambdaMapComonoid_hom {K L : SSet.{u}} (a : K ⟶ L)
    (x y : CubicalLambda A K) :
    (cubicalLambdaMapComonoid A a x y).hom = (cubicalLambdaMap A a).map x y := rfl

end SerrePositivity.KST.SConstruction
