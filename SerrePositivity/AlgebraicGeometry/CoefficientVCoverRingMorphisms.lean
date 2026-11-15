module

public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverRingModel

/-!
概要：模型の圏の射を、実際の環の射とその可換式で扱う。
方針：係数と可換な環の射を代数写像に移し、両辺の射で一致を判定する。
規約：模型の基底・始域・元の写像への可換式を保つ。
使われ方：B03・B04 の実際の係数遷移を模型の関手へ束ねる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {k R C : Type u} [CommRing k] [CommRing R] [CommRing C]
  [Algebra k R] [Algebra k C] (g : R →ₐ[k] C)

/-- 実際の環の二射と係数・三つの可換式から、模型の圏の射を作る。 -/
def coefficientVCoverModelHomMkOfRingHoms {X Y : CoefficientVCoverModelCategory k g}
    (a : X.obj.left.left.obj →+* Y.obj.left.left.obj)
    (d : X.obj.left.right.obj →+* Y.obj.left.right.obj)
    (hκa : a.comp (algebraMap k X.obj.left.left.obj) = algebraMap k Y.obj.left.left.obj)
    (hκd : d.comp (algebraMap k X.obj.left.right.obj) = algebraMap k Y.obj.left.right.obj)
    (ht : Y.obj.left.hom.hom.hom.toRingHom.comp a =
      d.comp X.obj.left.hom.hom.hom.toRingHom)
    (ha : Y.obj.hom.left.hom.toRingHom.comp a = X.obj.hom.left.hom.toRingHom)
    (hd : Y.obj.hom.right.hom.toRingHom.comp d = X.obj.hom.right.hom.toRingHom) : X ⟶ Y := by
  let a' : X.obj.left.left.obj →ₐ[k] Y.obj.left.left.obj :=
    { __ := a, commutes' := fun x ↦ DFunLike.congr_fun hκa x }
  let d' : X.obj.left.right.obj →ₐ[k] Y.obj.left.right.obj :=
    { __ := d, commutes' := fun x ↦ DFunLike.congr_fun hκd x }
  exact coefficientVCoverModelHomMk g a' d' (AlgHom.toRingHom_injective ht)
    (AlgHom.toRingHom_injective ha) (AlgHom.toRingHom_injective hd)

/-- 模型の圏の射は、基底と始域の両方の環の射で決まる。 -/
theorem coefficientVCoverModelHom_ext {X Y : CoefficientVCoverModelCategory k g}
    {a b : X ⟶ Y}
    (ha : a.hom.left.left.hom.hom.toRingHom = b.hom.left.left.hom.hom.toRingHom)
    (hd : a.hom.left.right.hom.hom.toRingHom = b.hom.left.right.hom.hom.toRingHom) : a = b := by
  apply InducedCategory.hom_ext
  apply CostructuredArrow.hom_ext
  apply Arrow.hom_ext
  · apply InducedCategory.hom_ext
    exact CommAlgCat.hom_ext (AlgHom.toRingHom_injective ha)
  · apply InducedCategory.hom_ext
    exact CommAlgCat.hom_ext (AlgHom.toRingHom_injective hd)

end SerrePositivity.AlgebraicGeometry
