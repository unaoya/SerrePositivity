module

public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverModelCategory
public import Mathlib.RingTheory.FinitePresentation

/-!
概要：小さい被覆模型の実際の環に係数代数構造と有限型性・Noether 性を供給する。
方針：有限生成代数のデータを同じ環へ移し、Noether 基底上の有限型性から有限表示性を得る。
規約：元の R,C の Noether 性と g の有限表示性は要求しない。
使われ方：B03・B04 の各 Noether 模型と素体上の有限型模型の供給。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable (k : Type u) [CommRing k]
  {R C : Type u} [CommRing R] [CommRing C] [Algebra k R] [Algebra k C] (g : R →ₐ[k] C)

instance coefficientVCoverModelSmallBase_algebra (i : CoefficientVCoverModelIndex k g) :
    Algebra k ((coefficientVCoverModelSmallArrowDiagram k g).obj i).left :=
  inferInstanceAs (Algebra k ((equivSmallModel (CoefficientVCoverModelCategory k g)).inverse.obj i).obj.left.left.obj)

instance coefficientVCoverModelSmallSource_algebra (i : CoefficientVCoverModelIndex k g) :
    Algebra k ((coefficientVCoverModelSmallArrowDiagram k g).obj i).right :=
  inferInstanceAs (Algebra k ((equivSmallModel (CoefficientVCoverModelCategory k g)).inverse.obj i).obj.left.right.obj)

instance coefficientVCoverModelSmallBase_finiteType (i : CoefficientVCoverModelIndex k g) :
    Algebra.FiniteType k ((coefficientVCoverModelSmallArrowDiagram k g).obj i).left :=
  inferInstanceAs (Algebra.FiniteType k
    ((equivSmallModel (CoefficientVCoverModelCategory k g)).inverse.obj i).obj.left.left.obj)

instance coefficientVCoverModelSmallSource_finiteType (i : CoefficientVCoverModelIndex k g) :
    Algebra.FiniteType k ((coefficientVCoverModelSmallArrowDiagram k g).obj i).right :=
  inferInstanceAs (Algebra.FiniteType k
    ((equivSmallModel (CoefficientVCoverModelCategory k g)).inverse.obj i).obj.left.right.obj)

/-- 各段の実際の環写像は affine v 判定を満たす。 -/
theorem coefficientVCoverModelSmallArrow_vCover (i : CoefficientVCoverModelIndex k g) :
    IsAffineVCover ((coefficientVCoverModelSmallArrowDiagram k g).obj i).hom.hom :=
  ((equivSmallModel (CoefficientVCoverModelCategory k g)).inverse.obj i).property

/-- 各段の環写像は、模型の同じ k 構造と可換。 -/
theorem coefficientVCoverModelSmallArrow_comp_algebraMap (i : CoefficientVCoverModelIndex k g) :
    ((coefficientVCoverModelSmallArrowDiagram k g).obj i).hom.hom.comp
      (algebraMap k ((coefficientVCoverModelSmallArrowDiagram k g).obj i).left) =
      algebraMap k ((coefficientVCoverModelSmallArrowDiagram k g).obj i).right :=
  ((equivSmallModel (CoefficientVCoverModelCategory k g)).inverse.obj i).obj.left.hom.hom.hom.comp_algebraMap

instance coefficientVCoverModelSmallBase_noetherian [IsNoetherianRing k]
    (i : CoefficientVCoverModelIndex k g) :
    IsNoetherianRing ((coefficientVCoverModelSmallArrowDiagram k g).obj i).left :=
  Algebra.FiniteType.isNoetherianRing k _

instance coefficientVCoverModelSmallSource_noetherian [IsNoetherianRing k]
    (i : CoefficientVCoverModelIndex k g) :
    IsNoetherianRing ((coefficientVCoverModelSmallArrowDiagram k g).obj i).right :=
  Algebra.FiniteType.isNoetherianRing k _

private theorem finitePresentation_algHom_of_finiteType
    {k A D : Type u} [CommRing k] [IsNoetherianRing k] [CommRing A] [CommRing D]
    [Algebra k A] [Algebra k D] [Algebra.FiniteType k A] [Algebra.FiniteType k D]
    (t : A →ₐ[k] D) : t.toRingHom.FinitePresentation := by
  letI : Algebra A D := t.toRingHom.toAlgebra
  letI : IsScalarTower k A D := IsScalarTower.of_algebraMap_eq' t.comp_algebraMap.symm
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  apply RingHom.FinitePresentation.of_finiteType.mp
  exact Algebra.FiniteType.of_restrictScalars_finiteType k A D

/-- 各段の実際の環写像は、Noether な係数環上では有限表示。 -/
theorem coefficientVCoverModelSmallArrow_finitePresentation [IsNoetherianRing k]
    (i : CoefficientVCoverModelIndex k g) :
    ((coefficientVCoverModelSmallArrowDiagram k g).obj i).hom.hom.FinitePresentation :=
  finitePresentation_algHom_of_finiteType
    (A := ((equivSmallModel (CoefficientVCoverModelCategory k g)).inverse.obj i).obj.left.left.obj)
    (D := ((equivSmallModel (CoefficientVCoverModelCategory k g)).inverse.obj i).obj.left.right.obj)
    ((equivSmallModel (CoefficientVCoverModelCategory k g)).inverse.obj i).obj.left.hom.hom.hom

end SerrePositivity.AlgebraicGeometry
