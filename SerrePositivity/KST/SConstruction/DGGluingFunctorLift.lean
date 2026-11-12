module
public import SerrePositivity.KST.SConstruction.DGHomIsoFunctorLiftOfEq
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Category

/-! # 元の代表加群 comma 表示から実 dg gluing への関手
概要：元の comma 値関手を、指定した両成分と閉比較を持つ同じ gluing 対象へ移す。
方針：元の全 Hom 鎖同型の逆で作用を持ち上げ、単位・合成と実 factorization を回収する。
規約：全次数作用を保持し、gluing の前三角性は仮定しない。使われ方：標準対角 dg 関手。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  {P : Type t} [DGCategory R P]
  (F : DGFunctor R P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R D (RightModule R C) M.toFunctor))
  (b : P → _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (v : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ≅
    ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (b x)))

/-- 元の comma 値関手を、指定した同じ代表対象へ閉零同型で共役した関手。 -/
def dgGluingLiftCommaTarget := dgHomIsoLiftTarget R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M) F b v

/-- 元の全 Hom 作用を、元の鎖同型の逆で実 dg gluing へ持ち上げる。 -/
def dgGluingFunctorLift : DGFunctor R P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  dgHomIsoFunctorLift R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M) (fun _ _ => rfl) F b v

/-- 同じ持ち上げは、指定した両成分と閉比較を持つ対象そのものを回収する。 -/
lemma dgGluingFunctorLift_obj (x : P) :
    (dgGluingFunctorLift R C D M F b v).obj x = b x := rfl

/-- 同じ持ち上げの全 Hom 作用は、元の comma 作用と同じ鎖同型の逆。 -/
lemma dgGluingFunctorLift_map (x y : P) :
    (dgGluingFunctorLift R C D M F b v).map x y =
      (dgGluingLiftCommaTarget R C D M F b v).map x y ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M (b x) (b y)).inv := rfl

/-- 元の comma 表示へ送ると、元の閉零同型による共役関手を厳密に回収する。 -/
lemma dgGluingFunctorLift_toComma :
    (dgGluingFunctorLift R C D M F b v).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M) =
      dgGluingLiftCommaTarget R C D M F b v :=
  dgHomIsoFunctorLift_factor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M) (fun _ _ => rfl) F b v

/-- 同じ右射影の対象値は、元の指定した右成分そのもの。 -/
lemma dgGluingFunctorLift_right_obj (x : P) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D M).obj ((dgGluingFunctorLift R C D M F b v).obj x) =
      (b x).right := rfl

/-- 同じ左加群射影の対象値は、元の指定した左成分の同じ代表加群。 -/
lemma dgGluingFunctorLift_leftModule_obj (x : P) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeftModule R C D M).obj ((dgGluingFunctorLift R C D M F b v).obj x) =
      representable R (b x).left := rfl

/-- 元の comma 作用を回収する全 Hom 鎖写像は、同じ持ち上げの作用に一意に一致する。 -/
lemma dgGluingFunctorLift_map_unique (x y : P)
    (k : homObject R P x y ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomComplex R C D M (b x) (b y))
    (hk : k ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M (b x) (b y)).hom =
      (dgGluingLiftCommaTarget R C D M F b v).map x y) :
    k = (dgGluingFunctorLift R C D M F b v).map x y :=
  dgHomIsoFunctorLift_map_unique R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M) (fun _ _ => rfl) F b v x y k hk

variable (h : ∀ x, F.obj x = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaObject R C D M (b x))

/-- 同じ対象像の厳密な一致から作る、元の comma 関手の実 gluing 持ち上げ。 -/
def dgGluingFunctorLiftOfEq : DGFunctor R P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :=
  dgHomIsoFunctorLiftOfEq R F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M) (fun _ _ => rfl) b h

/-- 同じ対象等号の持ち上げは、元の実 comma 値関手そのものを厳密に回収する。 -/
lemma dgGluingFunctorLiftOfEq_toComma :
    (dgGluingFunctorLiftOfEq R C D M F b h).comp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M) = F :=
  dgHomIsoFunctorLiftOfEq_factor R F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingToComma R C D M)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomRepresentableIso R C D M) (fun _ _ => rfl) b h

end SerrePositivity.KST.SConstruction
