module

public import SerrePositivity.AlgebraicGeometry.CoefficientModelCategory
public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverRingModel

/-!
概要：全模型から実際の環表示の有限型被覆模型への射を登録する。
方針：係数に関して可換な二環の射を代数写像へ移し、同じ被覆模型を標的にする。
規約：旧模型の二射と全ての可換式を保持する。
使われ方：B03・B04 の被覆模型の final 性の実際の証人。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {k R C : Type u} [CommRing k] [CommRing R] [CommRing C]
  [Algebra k R] [Algebra k C]

/-- 全模型の環の二射と係数・三つの可換式から、模型の射を作る。 -/
def coefficientModelHomMkOfRingHoms (g : R →ₐ[k] C)
    {X Y : CoefficientModelCategory k g}
    (a : X.left.left.obj →+* Y.left.left.obj) (d : X.left.right.obj →+* Y.left.right.obj)
    (hκa : a.comp (algebraMap k X.left.left.obj) = algebraMap k Y.left.left.obj)
    (hκd : d.comp (algebraMap k X.left.right.obj) = algebraMap k Y.left.right.obj)
    (ht : Y.left.hom.hom.hom.toRingHom.comp a = d.comp X.left.hom.hom.hom.toRingHom)
    (ha : Y.hom.left.hom.toRingHom.comp a = X.hom.left.hom.toRingHom)
    (hd : Y.hom.right.hom.toRingHom.comp d = X.hom.right.hom.toRingHom) : X ⟶ Y := by
  let a' : X.left.left.obj →ₐ[k] Y.left.left.obj :=
    { __ := a, commutes' := fun x ↦ DFunLike.congr_fun hκa x }
  let d' : X.left.right.obj →ₐ[k] Y.left.right.obj :=
    { __ := d, commutes' := fun x ↦ DFunLike.congr_fun hκd x }
  exact coefficientModelHomMk g a' d' (AlgHom.toRingHom_injective ht)
    (AlgHom.toRingHom_injective ha) (AlgHom.toRingHom_injective hd)

/-- 全模型の両辺の環の射は、同じ実際の被覆模型への射を与える。 -/
def coefficientModelHomToRingCoverModel (g : R →ₐ[k] C) (X : CoefficientModelCategory k g)
    {A D : Type u} [CommRing A] [CommRing D]
    (κA : k →+* A) (κD : k →+* D) (hA : κA.FiniteType) (hD : κD.FiniteType)
    (t : A →+* D) (a : A →+* R) (d : D →+* C)
    (hκt : t.comp κA = κD) (hκa : a.comp κA = algebraMap k R)
    (hκd : d.comp κD = algebraMap k C)
    (hsq : d.comp t = g.toRingHom.comp a) (hv : IsAffineVCover t)
    (a₀ : X.left.left.obj →+* A) (d₀ : X.left.right.obj →+* D)
    (hκa₀ : a₀.comp (algebraMap k X.left.left.obj) = κA)
    (hκd₀ : d₀.comp (algebraMap k X.left.right.obj) = κD)
    (ht : t.comp a₀ = d₀.comp X.left.hom.hom.hom.toRingHom)
    (ha : a.comp a₀ = X.hom.left.hom.toRingHom)
    (hd : d.comp d₀ = X.hom.right.hom.toRingHom) :
    X ⟶ (coefficientVCoverModelObjOfRingHoms g κA κD hA hD t a d hκt hκa hκd hsq hv).obj := by
  exact coefficientModelHomMkOfRingHoms g a₀ d₀ hκa₀ hκd₀ ht ha hd

end SerrePositivity.AlgebraicGeometry
