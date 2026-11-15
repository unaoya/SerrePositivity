module

public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverModelCategory

/-!
概要：実際の有限型 v 被覆模型と可換な正方形を、被覆模型の圏へ登録する。
方針：両辺の代数写像と元の写像への可換式を Arrow と costructured arrow に束ねる。
規約：模型の基底と始域の双方の写像を保持し、被覆性は実際の射に課す。
使われ方：B03・B04 の共同後段と平行射の一致の組立て。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable {k R C : Type u} [CommRing k] [CommRing R] [CommRing C]
  [Algebra k R] [Algebra k C]
variable (g : R →ₐ[k] C)

/-- 有限型模型の実際の射と元の写像への可換な正方形を登録する。 -/
def coefficientVCoverModelObj
    {A D : Type u} [CommRing A] [CommRing D] [Algebra k A] [Algebra k D]
    [Algebra.FiniteType k A] [Algebra.FiniteType k D]
    (t : A →ₐ[k] D) (a : A →ₐ[k] R) (d : D →ₐ[k] C)
    (h : d.comp t = g.comp a) (ht : IsAffineVCover t.toRingHom) :
    CoefficientVCoverModelCategory k g := by
  let M : Arrow (FGAlgCat.{u} k) := Arrow.mk
    (ObjectProperty.homMk (CommAlgCat.ofHom t) :
      (⟨CommAlgCat.of k A, inferInstance⟩ : FGAlgCat.{u} k) ⟶
      (⟨CommAlgCat.of k D, inferInstance⟩ : FGAlgCat.{u} k))
  refine ⟨CostructuredArrow.mk (Y := M)
    (Arrow.homMk (CommAlgCat.ofHom a) (CommAlgCat.ofHom d)
      (CommAlgCat.hom_ext h.symm)), ?_⟩
  exact ht

/-- 基底と始域の写像と三つの可換式から、実際の模型の間の射を作る。 -/
def coefficientVCoverModelHomMk {X Y : CoefficientVCoverModelCategory k g}
    (a : X.obj.left.left.obj →ₐ[k] Y.obj.left.left.obj)
    (d : X.obj.left.right.obj →ₐ[k] Y.obj.left.right.obj)
    (ht : Y.obj.left.hom.hom.hom.comp a = d.comp X.obj.left.hom.hom.hom)
    (ha : Y.obj.hom.left.hom.comp a = X.obj.hom.left.hom)
    (hd : Y.obj.hom.right.hom.comp d = X.obj.hom.right.hom) : X ⟶ Y := by
  let sq : X.obj.left ⟶ Y.obj.left := Arrow.homMk
    (ObjectProperty.homMk (CommAlgCat.ofHom a))
    (ObjectProperty.homMk (CommAlgCat.ofHom d))
    (by apply InducedCategory.hom_ext; exact CommAlgCat.hom_ext ht)
  refine ObjectProperty.homMk (CostructuredArrow.homMk sq ?_)
  apply Arrow.hom_ext
  · exact CommAlgCat.hom_ext ha
  · exact CommAlgCat.hom_ext hd

/-- 恒等模型は、任意の元の環写像への可換な正方形を持つ。 -/
instance : Nonempty (CoefficientVCoverModelCategory k g) := by
  refine ⟨coefficientVCoverModelObj g (AlgHom.id k k)
    (Algebra.ofId k R) (Algebra.ofId k C) ?_ isAffineVCover_id⟩
  ext

end SerrePositivity.AlgebraicGeometry
