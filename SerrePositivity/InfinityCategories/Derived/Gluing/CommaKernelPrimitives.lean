module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommaKernelCompositionMaps

/-! 加群 comma 比較は、全 Hom tensor 上の合成の第三 cochain を保つ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded MonoidalCategory CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (X Y Z : DGFunctorCommaObject R D (RightModule R C) M.toFunctor)
local notation "F" => Morita.kernelTensor R D C M
local notation "KX" => dgGluingCommaKernelObject R C D M X
local notation "KY" => dgGluingCommaKernelObject R C D M Y
local notation "KZ" => dgGluingCommaKernelObject R C D M Z
local notation "aXY" => Iso.hom (dgGluingCommaKernelHomIso R C D M X Y)
local notation "aYZ" => Iso.hom (dgGluingCommaKernelHomIso R C D M Y Z)
local notation "aXZ" => Iso.hom (dgGluingCommaKernelHomIso R C D M X Z)
local notation "cXY" => Iso.hom (dgGluingCommaKernelTargetIso R C D M X Y)
local notation "cYZ" => Iso.hom (dgGluingCommaKernelTargetIso R C D M Y Z)
local notation "cXZ" => Iso.hom (dgGluingCommaKernelTargetIso R C D M X Z)

/-- 第一 primitive は同じ列比較によって厳密に輸送される。 -/
lemma dgGluingCommaKernelFirstCompositePrimitive :
    (Cochain.ofHom (aXY ⊗ₘ aYZ)).comp
      (dgFunctorCommaFirstCompositePrimitive R (RightModule R D) (RightModule R C)
        F KX KY KZ) (zero_add (-1)) =
    (dgFunctorCommaFirstCompositePrimitive R D (RightModule R C) M.toFunctor X Y Z).comp
      (Cochain.ofHom (cXZ)) (add_zero (-1)) :=
  dgGluingTensorRightPrimitive_transport (-1) (aXY) (aYZ) (cXY) (cXZ) _ _ _ _
    (dgGluingCommaKernelHomIso_primitive R C D M X Y)
    (dgGluingCommaKernelFirstCompositionMap R C D M X Y Z)

/-- 第二 primitive も、同じ列比較で全次数を保持して輸送される。 -/
lemma dgGluingCommaKernelSecondCompositePrimitive :
    (Cochain.ofHom (aXY ⊗ₘ aYZ)).comp
      (dgFunctorCommaSecondCompositePrimitive R (RightModule R D) (RightModule R C)
        F KX KY KZ) (zero_add (-1)) =
    (dgFunctorCommaSecondCompositePrimitive R D (RightModule R C) M.toFunctor X Y Z).comp
      (Cochain.ofHom (cXZ)) (add_zero (-1)) :=
  dgGluingTensorLeftPrimitive_transport (-1) (aXY) (aYZ) (cYZ) (cXZ) _ _ _ _
    (dgGluingCommaKernelHomIso_primitive R C D M Y Z)
    (dgGluingCommaKernelSecondCompositionMap R C D M X Y Z)

/-- 二項の和としての合成の第三 cochain も、厳密に輸送される。 -/
lemma dgGluingCommaKernelCompositePrimitive :
    (Cochain.ofHom (aXY ⊗ₘ aYZ)).comp
      (dgFunctorCommaCompositePrimitive R (RightModule R D) (RightModule R C)
        F KX KY KZ) (zero_add (-1)) =
    (dgFunctorCommaCompositePrimitive R D (RightModule R C) M.toFunctor X Y Z).comp
      (Cochain.ofHom (cXZ)) (add_zero (-1)) := by
  simp only [dgFunctorCommaCompositePrimitive, Cochain.comp_add, Cochain.add_comp]
  rw [dgGluingCommaKernelFirstCompositePrimitive, dgGluingCommaKernelSecondCompositePrimitive]

end SerrePositivity.InfinityCategories
