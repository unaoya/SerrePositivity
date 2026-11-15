module

public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverModelCategory

/-!
概要：v 判定を課す前の有限型係数模型の全体を、実際の可換正方形の圏として扱う。
方針：既存の被覆模型の ambient な costructured arrow をそのまま用いる。
規約：両辺の実際の有限型代数と元の g への可換式を保持する。
使われ方：B03・B04 の全模型の filtered 性と被覆模型への final な包含。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable (k : Type u) [CommRing k]
  {R C : Type u} [CommRing R] [CommRing C] [Algebra k R] [Algebra k C]
  (g : R →ₐ[k] C)

/-- 有限型な二代数の射と、元の g への実際の可換な正方形の圏。 -/
abbrev CoefficientModelCategory :=
  CostructuredArrow (coefficientVCoverModelFGInclusion k) (Arrow.mk (CommAlgCat.ofHom g))

instance : EssentiallySmall.{u} (CoefficientModelCategory k g) := inferInstanceAs
  (EssentiallySmall.{u} (CostructuredArrow (coefficientVCoverModelFGInclusion k)
    (Arrow.mk (CommAlgCat.ofHom g))))

variable {k}

/-- 有限型な二代数と元の g への可換な正方形を全模型の圏へ登録する。 -/
def coefficientModelObj
    {A D : Type u} [CommRing A] [CommRing D] [Algebra k A] [Algebra k D]
    [Algebra.FiniteType k A] [Algebra.FiniteType k D]
    (t : A →ₐ[k] D) (a : A →ₐ[k] R) (d : D →ₐ[k] C)
    (h : d.comp t = g.comp a) : CoefficientModelCategory k g := by
  let M : Arrow (FGAlgCat.{u} k) := Arrow.mk
    (ObjectProperty.homMk (CommAlgCat.ofHom t) :
      (⟨CommAlgCat.of k A, inferInstance⟩ : FGAlgCat.{u} k) ⟶
      (⟨CommAlgCat.of k D, inferInstance⟩ : FGAlgCat.{u} k))
  exact CostructuredArrow.mk (Y := M)
    (Arrow.homMk (CommAlgCat.ofHom a) (CommAlgCat.ofHom d) (CommAlgCat.hom_ext h.symm))

/-- 二つの代数写像と三つの可換式から、全模型の圏の射を作る。 -/
def coefficientModelHomMk {X Y : CoefficientModelCategory k g}
    (a : X.left.left.obj →ₐ[k] Y.left.left.obj)
    (d : X.left.right.obj →ₐ[k] Y.left.right.obj)
    (ht : Y.left.hom.hom.hom.comp a = d.comp X.left.hom.hom.hom)
    (ha : Y.hom.left.hom.comp a = X.hom.left.hom)
    (hd : Y.hom.right.hom.comp d = X.hom.right.hom) : X ⟶ Y := by
  let sq : X.left ⟶ Y.left := Arrow.homMk
    (ObjectProperty.homMk (CommAlgCat.ofHom a)) (ObjectProperty.homMk (CommAlgCat.ofHom d))
    (by apply InducedCategory.hom_ext; exact CommAlgCat.hom_ext ht)
  refine CostructuredArrow.homMk sq ?_
  apply Arrow.hom_ext
  · exact CommAlgCat.hom_ext ha
  · exact CommAlgCat.hom_ext hd

/-- 全模型の射は両辺の代数写像によって決まる。 -/
theorem coefficientModelHom_ext {X Y : CoefficientModelCategory k g} {f h : X ⟶ Y}
    (ha : f.left.left.hom.hom = h.left.left.hom.hom)
    (hd : f.left.right.hom.hom = h.left.right.hom.hom) : f = h := by
  apply CostructuredArrow.hom_ext
  apply Arrow.hom_ext
  · apply InducedCategory.hom_ext
    exact CommAlgCat.hom_ext ha
  · apply InducedCategory.hom_ext
    exact CommAlgCat.hom_ext hd

/-- 模型の正方形の可換式を、代数写像として読む。 -/
theorem coefficientModel_comm (X : CoefficientModelCategory k g) :
    X.hom.right.hom.comp X.left.hom.hom.hom = g.comp X.hom.left.hom :=
  (congrArg CommAlgCat.Hom.hom X.hom.w).symm

/-- 全模型の射の基底側の三角形。 -/
theorem coefficientModelHom_base_triangle {X Y : CoefficientModelCategory k g} (f : X ⟶ Y) :
    Y.hom.left.hom.comp f.left.left.hom.hom = X.hom.left.hom :=
  congrArg CommAlgCat.Hom.hom (congrArg Arrow.Hom.left f.w)

/-- 全模型の射の始域側の三角形。 -/
theorem coefficientModelHom_source_triangle {X Y : CoefficientModelCategory k g} (f : X ⟶ Y) :
    Y.hom.right.hom.comp f.left.right.hom.hom = X.hom.right.hom :=
  congrArg CommAlgCat.Hom.hom (congrArg Arrow.Hom.right f.w)

instance : Nonempty (CoefficientModelCategory k g) := by
  refine ⟨coefficientModelObj g (AlgHom.id k k) (Algebra.ofId k R) (Algebra.ofId k C) ?_⟩
  ext

end SerrePositivity.AlgebraicGeometry
