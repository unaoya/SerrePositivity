module
public import SerrePositivity.KST.SConstruction.FamilyCylinderEndpointAdjustment
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy

/-! # 全 raw 円柱と指定境界を保持する比較の持ち上げ
概要：全単射の RLP を持つ射に沿い、元の全基底円柱と両端・指定境界を保つ比較を得る。
方針：元の区間境界を先に持ち上げ、同じ全射影を保つ相対延長で指定境界を合わせる。
規約：基底円柱を定数と仮定せず、全時刻の射影をそのまま回収する。
使われ方：元の全段 raw 比較から、指定 BF 境界付きの全族比較を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel
open LargeParameterHomotopy
open scoped Simplicial

/-- 元の二端点の境界写像の後合成は、同じ二つの後合成端点の全境界写像。 -/
lemma familyBoundaryMap_post {U E B : SSet.{u}} (p : E ⟶ B) (a b : U ⟶ E) :
    boundaryMap a b ≫ p = boundaryMap (a ≫ p) (b ≫ p) := by
  apply (boundaryColimit U).hom_ext
  rintro ⟨k⟩
  cases k
  · change (U ◁ SSet.boundary.ι (1 : Fin 2)) ≫ (boundaryMap a b ≫ p) =
      (U ◁ SSet.boundary.ι (1 : Fin 2)) ≫ boundaryMap (a ≫ p) (b ≫ p)
    rw [boundaryMap_zero_assoc, boundaryMap_zero]
  · change (U ◁ SSet.boundary.ι (0 : Fin 2)) ≫ (boundaryMap a b ≫ p) =
      (U ◁ SSet.boundary.ι (0 : Fin 2)) ≫ boundaryMap (a ≫ p) (b ≫ p)
    rw [boundaryMap_one_assoc, boundaryMap_one]

/-- 元の区間境界を回収する写像を、同じ両端の実円柱として表示する。 -/
def familyHomotopyOfBoundary {U E : SSet.{u}} (a b : U ⟶ E)
    (q : U ⊗ (Δ[1] : SSet.{u}) ⟶ E)
    (hq : (U ◁ (SSet.boundary 1).ι) ≫ q = boundaryMap a b) : SSet.Homotopy a b where
  h := q
  h₀ := by
    change SSet.ι₀ ≫ q = a
    rw [← section_zero U, Category.assoc, ← SSet.boundary.ι_ι (1 : Fin 2),
      whiskerLeft_comp, Category.assoc, hq, boundaryMap_zero]
    rfl
  h₁ := by
    change SSet.ι₁ ≫ q = b
    rw [← section_one U, Category.assoc, ← SSet.boundary.ι_ι (0 : Fin 2),
      whiskerLeft_comp, Category.assoc, hq, boundaryMap_one]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 元の全基底比較円柱を、同じ二端点を保って全時刻で持ち上げる。 -/
def rawHomotopyLiftData {U E B : SSet.{u}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p)
    (a b : U ⟶ E) (H : SSet.Homotopy (a ≫ p) (b ≫ p)) :
    {K : SSet.Homotopy a b // K.h ≫ p = H.h} := by
  let j := U ◁ (SSet.boundary 1).ι
  let : HasLiftingProperty j p := hp j inferInstance
  let sq : CommSq (boundaryMap a b) j p H.h :=
    ⟨(familyBoundaryMap_post p a b).trans (HomotopyEndpointComparison.boundary_eq H).symm⟩
  exact ⟨familyHomotopyOfBoundary a b sq.lift sq.fac_left, sq.fac_right⟩

/-- 先に指定した境界の実比較円柱と元の全基底円柱を同時に保つ持ち上げ。 -/
def prescribedRawHomotopyLiftData {U T E B : SSet.{u}} (p : E ⟶ B)
    (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p) (j : T ⟶ U) [Mono j]
    (a b : U ⟶ E) (H : SSet.Homotopy (a ≫ p) (b ≫ p))
    (A : SSet.Homotopy (j ≫ a) (j ≫ b))
    (hA : A.h ≫ p = (j ▷ (Δ[1] : SSet.{u})) ≫ H.h) :
    {K : SSet.Homotopy a b // K.h ≫ p = H.h ∧
      (j ▷ (Δ[1] : SSet.{u})) ≫ K.h = A.h} := by
  let D := rawHomotopyLiftData p hp a b H
  have ha : A.h ≫ p = (j ▷ (Δ[1] : SSet.{u})) ≫ D.val.h ≫ p := by
    rw [D.property]
    exact hA
  let ex := MonoRightLiftingRelativeHomotopy.exists_extension p hp j D.val A ha
  exact ⟨ex.choose, ex.choose_spec.1.trans D.property, ex.choose_spec.2⟩

end SerrePositivity.KST.SConstruction
