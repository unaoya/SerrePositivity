module

public import SerrePositivity.InfinityCategories.F1.Yoneda.RepresentablePresheafValues
public import SerrePositivity.InfinityCategories.F1.Yoneda.YonedaInfinityFullyFaithful
public import SerrePositivity.InfinityCategories.F1.Simplicial.SSetProductEvaluation

/-!
概要：元の twisted arrow から得た二変数 Hom 関手の両制限・値・curry を明示する。
方針：同じ共同評価を使い、値は元の表現可能前層の値の比較へ戻す。
規約：独立な Hom 図式を選び直さず、混合する全高次単体を保持する。
使われ方：F1-3b、Kerodon 8、HTT 5.1.3。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {C : SSet.{u}} [Quasicategory C]

/-- 同じ二変数 Hom 関手の指定対象対での値は、元の標準右写像空間と同値。 -/
def homInfinityJointValueEquivalence (x y : C _⦋0⦌) :
    QCatEquivalence
      (spaceInfinityObject ((homInfinityJointEvaluation C).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm x), ULift.up y))).obj (pinchedHom x y) :=
  by
    have h : (representablePresheafInfinity y).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm x)) =
        (homInfinityJointEvaluation C).app (Opposite.op ⦋0⦌)
          (ULift.up (SSet.opObjEquiv.symm x), ULift.up y) := by
      dsimp only [representablePresheafInfinity]
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, ssetLift_apply,
        ssetConst_zero_apply, NatTrans.id_app, ConcreteCategory.id_apply]
    rw [← h]
    exact representablePresheafValueEquivalence x y

/-- 分離前の同じ twisted arrow 分類図式の値も、元の同じ写像空間と同値。 -/
def twistedArrowHomValueEquivalence (x y : C _⦋0⦌) :
    QCatEquivalence
      (spaceInfinityObject ((twistedArrowHomInfinity C).app (Opposite.op ⦋0⦌)
        (ULift.up (SSet.opObjEquiv.symm x, y)))).obj (pinchedHom x y) :=
  homInfinityJointValueEquivalence x y

/-- 第一変数を固定した、元の二変数 Hom の共変な制限。 -/
def homInfinityCovariant (x : C _⦋0⦌) :
    (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ SpaceInfinity.{u} :=
  lift (SSet.const (ULift.up (SSet.opObjEquiv.symm x)))
    (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj C)) ≫ homInfinityJointEvaluation C

/-- 同じ共変制限は、元の Yoneda 関手を同じ対象で評価した実際の合成。 -/
lemma homInfinityCovariant_eq_yonedaEvaluation (x : C _⦋0⦌) :
    homInfinityCovariant x = yonedaInfinityMap C ≫ presheafInfinityEvaluation x := by
  rw [homInfinityCovariant, ← yonedaInfinityMap_uncurry]
  apply SSet.hom_ext
  intro n
  rfl

/-- 同じ共変制限の値は元の標準写像空間。 -/
def homInfinityCovariantValueEquivalence (x y : C _⦋0⦌) :
    QCatEquivalence
      (spaceInfinityObject ((homInfinityCovariant x).app (Opposite.op ⦋0⦌) (ULift.up y))).obj
      (pinchedHom x y) :=
  by
    have h : (homInfinityCovariant x).app (Opposite.op ⦋0⦌) (ULift.up y) =
        (homInfinityJointEvaluation C).app (Opposite.op ⦋0⦌)
          (ULift.up (SSet.opObjEquiv.symm x), ULift.up y) := by
      dsimp only [homInfinityCovariant]
      simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, ssetLift_apply,
        ssetConst_zero_apply, NatTrans.id_app, ConcreteCategory.id_apply]
    rw [h]
    exact homInfinityJointValueEquivalence x y

/-- 第一変数に関する反変性を、共変 Hom 関手の図式として curry した同じ共同評価。 -/
def coyonedaInfinityMap (C : SSet.{u}) [Quasicategory C] :
    (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj C)).obj SpaceInfinity.{u} :=
  curry ((β_ ((SSet.uliftFunctor.{u + 1, u}).obj C)
    ((SSet.uliftFunctor.{u + 1, u}).obj C.op)).hom ≫ homInfinityJointEvaluation C)

/-- 同じ co-Yoneda の全評価は、元の共同 Hom 評価の二変数を交換したもの。 -/
lemma coyonedaInfinityMap_uncurry (C : SSet.{u}) [Quasicategory C] :
    uncurry (coyonedaInfinityMap C) =
      (β_ ((SSet.uliftFunctor.{u + 1, u}).obj C)
        ((SSet.uliftFunctor.{u + 1, u}).obj C.op)).hom ≫ homInfinityJointEvaluation C :=
  uncurry_curry _

/-- 同じ co-Yoneda の指定頂点は、元の共同評価の同じ共変制限の図式。 -/
lemma coyonedaInfinityMap_vertex (x : C _⦋0⦌) :
    (coyonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up (SSet.opObjEquiv.symm x)) =
      functorVertex (homInfinityCovariant x) := by
  have h := (functorVertex_uncurry_at_vertex (coyonedaInfinityMap C)
    (ULift.up (SSet.opObjEquiv.symm x))).symm
  rw [coyonedaInfinityMap_uncurry] at h
  exact h

end SerrePositivity.InfinityCategories
