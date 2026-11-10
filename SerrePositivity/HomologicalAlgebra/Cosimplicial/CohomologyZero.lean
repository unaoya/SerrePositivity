module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.CupCohomology
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Cohomology

/-!
# 余単体的可換環の零次コホモロジー環

## 概要
二つの余面の等化部分環と零次コホモロジーを同一視する。

## 方針
零次には余境界がなく、Alexander–Whitney 積が等化部分環の積に一致することを使う。

## 規約
既存の零次コホモロジーの加法群を用いる。

## 使われ方
Hodge–Tate 写像の次数零。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial

universe u

namespace SerrePositivity.Cosimplicial

variable (X : CosimplicialObject CommRingCat.{u})

/-- 余単体次数零の二つの余面の等化部分環。 -/
abbrev zeroCocycleRing :=
  ((X.map (SimplexCategory.δ (0 : Fin 2))).hom).eqLocus
    ((X.map (SimplexCategory.δ (1 : Fin 2))).hom)

private theorem cochainDifferential_zero (x : X.obj ⦋0⦌) :
    cochainDifferential X 0 x =
      X.map (SimplexCategory.δ (0 : Fin 2)) x - X.map (SimplexCategory.δ (1 : Fin 2)) x := by
  rw [cochainDifferential_apply, Fin.sum_univ_two]
  simp [sub_eq_add_neg]

private def zeroCocyclesEquiv : zeroCocycleRing X ≃+ Cocycles X 0 where
  toFun x := ⟨x.1, by
    change (ringCochainComplex X).d 0 1 x.1 = 0
    rw [ringCochainComplex_d_apply X 0, cochainDifferential_zero]
    exact sub_eq_zero.mpr x.2⟩
  invFun x := ⟨x.1, by
    let x' : X.obj ⦋0⦌ := x.1
    have h : cochainDifferential X 0 x' = 0 :=
      (ringCochainComplex_d_apply X 0 x').symm.trans x.2
    exact sub_eq_zero.mp ((cochainDifferential_zero X x').symm.trans h)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

private theorem cohomologyClass_zero_injective : Function.Injective (cohomologyClass X 0) := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro a ha
  have h : cohomologyClass X 0 a = 0 := ha
  change (cohomologyQuotientIso X 0).inv (QuotientAddGroup.mk a) = 0 at h
  have h' := congrArg ((cohomologyQuotientIso X 0).hom) h
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply, map_zero] at h'
  exact boundary_zero X ((QuotientAddGroup.eq_zero_iff _).mp h')

/-- 等化部分環の加法群から零次コホモロジーへの標準同型。 -/
def cohomologyZeroAddEquiv : zeroCocycleRing X ≃+ cohomology X 0 :=
  (zeroCocyclesEquiv X).trans (AddEquiv.ofBijective (cohomologyClass X 0)
    ⟨cohomologyClass_zero_injective X, cohomologyClass_surjective X 0⟩)

private theorem cup_zero_zero (x y : X.obj ⦋0⦌) : cup X x y = x * y := by
  have hf : frontFace 0 0 = 𝟙 ⦋0⦌ := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    exact Subsingleton.elim (α := Fin 1) _ _
  have hb : backFace 0 0 = 𝟙 ⦋0⦌ := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    exact Subsingleton.elim (α := Fin 1) _ _
  simp [cup, hf, hb]

/-- 零次の同一視は積を cup 積へ送る。 -/
theorem cohomologyZeroAddEquiv_mul (a b : zeroCocycleRing X) :
    cohomologyZeroAddEquiv X (a * b) =
      cohomologyCup X (cohomologyZeroAddEquiv X a) (cohomologyZeroAddEquiv X b) := by
  change cohomologyClass X 0 (zeroCocyclesEquiv X (a * b)) =
    cohomologyCup X (cohomologyClass X 0 (zeroCocyclesEquiv X a))
      (cohomologyClass X 0 (zeroCocyclesEquiv X b))
  rw [cohomologyCup_class]
  congr 1
  apply Subtype.ext
  exact (cup_zero_zero X a.1 b.1).symm

/-- 零次コホモロジーの環構造は等化部分環から移す。 -/
instance cohomologyZeroCommRing : CommRing (cohomology X 0) := by
  let e := (cohomologyZeroAddEquiv X).symm
  letI : One (cohomology X 0) := ⟨e.symm 1⟩
  letI : Mul (cohomology X 0) := ⟨fun a b => e.symm (e a * e b)⟩
  letI : Pow (cohomology X 0) ℕ := ⟨fun a n => e.symm (e a ^ n)⟩
  letI : NatCast (cohomology X 0) := ⟨fun n => e.symm n⟩
  letI : IntCast (cohomology X 0) := ⟨fun n => e.symm n⟩
  exact e.injective.commRing e (map_zero e) (e.apply_symm_apply _)
    (map_add e) (fun _ _ => e.apply_symm_apply _) (map_neg e) (map_sub e)
    (fun n x => map_nsmul e n x) (fun n x => map_zsmul e n x)
    (fun _ _ => e.apply_symm_apply _) (fun _ => e.apply_symm_apply _)
    (fun _ => e.apply_symm_apply _)

/-- 零次コホモロジー環と余面の等化部分環の同型。 -/
def cohomologyZeroRingEquiv : cohomology X 0 ≃+* zeroCocycleRing X where
  __ := (cohomologyZeroAddEquiv X).symm
  map_mul' _ _ := (cohomologyZeroAddEquiv X).symm.apply_symm_apply _

end SerrePositivity.Cosimplicial
