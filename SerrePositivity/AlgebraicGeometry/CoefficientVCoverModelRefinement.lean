module

public import SerrePositivity.AlgebraicGeometry.CoefficientSquareBaseChange
public import SerrePositivity.AlgebraicGeometry.AffineVCoverCoefficientModel
public import SerrePositivity.AlgebraicGeometry.CoefficientPushoutArrowFactor
public import SerrePositivity.AlgebraicGeometry.CoefficientPushoutModelFunctor
public import SerrePositivity.AlgebraicGeometry.CoefficientModelRingCoverMap

/-!
概要：任意の全係数模型から、元の v 被覆の実際の有限型被覆模型への射を構成する。
方針：元の基底の有限表示 v 被覆を作り、被覆係数模型に旧正方形を同じ段で因子化する。
規約：元の g の有限表示性・元の R の Noether 性を仮定しない。
使われ方：B03・B04 の被覆模型の圏の filtered 性と final 性の証人。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
open _root_.AlgebraicGeometry
open scoped TensorProduct
universe u

/-- 任意の全模型は、元の v 被覆の実際の有限型被覆模型への射を持つ。 -/
theorem exists_coefficientModel_to_vCover
    (k : Type u) [CommRing k] [IsNoetherianRing k]
    {R C : Type u} [CommRing R] [CommRing C] [Algebra k R] [Algebra k C]
    (g : R →ₐ[k] C) (hv : IsAffineVCover g.toRingHom) (X : CoefficientModelCategory k g) :
    ∃ Y : CoefficientVCoverModelCategory k g, Nonempty (X ⟶ Y.obj) := by
  let A : Type u := X.left.left.obj
  let D : Type u := X.left.right.obj
  letI : CommRing A := inferInstanceAs (CommRing X.left.left.obj)
  letI : CommRing D := inferInstanceAs (CommRing X.left.right.obj)
  letI : Algebra k A := inferInstanceAs (Algebra k X.left.left.obj)
  letI : Algebra k D := inferInstanceAs (Algebra k X.left.right.obj)
  letI : Algebra.FiniteType k A := inferInstanceAs (Algebra.FiniteType k X.left.left.obj)
  letI : Algebra.FiniteType k D := inferInstanceAs (Algebra.FiniteType k X.left.right.obj)
  let t : A →ₐ[k] D := X.left.hom.hom.hom
  let a : A →ₐ[k] R := X.hom.left.hom
  let d : D →ₐ[k] C := X.hom.right.hom
  obtain ⟨P, _, _, hPfp, hPv, ι, p, hp, hd, hι⟩ :=
    exists_finitePresentation_baseChange_of_coefficient_square k A D R C t a d g
      (coefficientModel_comm g X) hv
  letI : Algebra.FinitePresentation R P := hPfp
  obtain ⟨B, hB, _, S, _, _, hSfp, hSv, ⟨e⟩⟩ :=
    exists_affineVCover_finitePresentation_coefficient_model k R P
      ((isSchemeVCover_specMap_iff _).mpr hPv)
  letI : Algebra.FinitePresentation B S := hSfp
  letI : Algebra.FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hB
  have hκ : (algebraMap k B).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
  have hκR : (algebraMap B R).comp (algebraMap k B) = algebraMap k R :=
    (IsScalarTower.algebraMap_eq k B R).symm
  have ha : a.toRingHom.comp (algebraMap k A) =
      (algebraMap B R).comp (algebraMap k B) := a.comp_algebraMap.trans hκR.symm
  have hS : IsAffineVCover (algebraMap B S) := (isSchemeVCover_specMap_iff _).mp hSv
  obtain ⟨j, a₀, d₀, hκa₀, hκd₀, ha₀, hd₀, ht₀⟩ :=
    exists_coefficientPushout_arrow_factor B R S e k A D (algebraMap k B) t a.toRingHom ι ha hι
  let M := coefficientPushoutVCoverModelFunctor k B R S g e (algebraMap k B) hκ hκR p hp hS
  let Y := M.obj j
  refine ⟨Y, ⟨?_⟩⟩
  apply coefficientModelHomMkOfRingHoms g a₀ d₀
  · exact hκa₀
  · exact hκd₀
  · exact ht₀
  · exact ha₀
  · change (p.comp ((coefficientPushoutRingCocone B R S e).ι.app j).hom).comp d₀ = d.toRingHom
    rw [RingHom.comp_assoc, hd₀, hd]

end SerrePositivity.AlgebraicGeometry
