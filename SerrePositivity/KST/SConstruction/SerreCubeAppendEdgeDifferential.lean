module
public import SerrePositivity.KST.SConstruction.SerreCubeBoundaryTensor

/-! # 元の全斉次元への辺付加の微分
概要：任意の元に辺を付けた元の微分を、微分への辺付加と元の右端二面差へ分解する。
方針：元の tensor 微分の Leibniz 則と元の辺の端点境界を評価する。
規約：元の斉次次数と右端面を保持。使われ方：全端点・辺 tensor 生成元の微分条件。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 任意の元の斉次元について、右端二面差は同じ端点差の tensor。 -/
lemma serreCubeFace_zero_difference (n : ℕ) (p : ℤ) (x : (serreCubeComplex A n).X p) :
    (serreCubeFace A true n 0).hom.f p x - (serreCubeFace A false n 0).hom.f p x =
      ιTensorObj (serreCubeComplex A n) (serreInterval A) p 0 p (add_zero p)
        (x ⊗ₜ[A] ((cycleFromUnit _ (serreIntervalOne A)).val -
          (cycleFromUnit _ (serreIntervalZero A)).val)) := by
  have h := congrArg₂ (fun y z => y - z)
    (serreCubeFace_zero_apply A true n p x) (serreCubeFace_zero_apply A false n p x)
  exact h.trans (by rw [TensorProduct.tmul_sub, map_sub]; rfl)

/-- 元の辺付加の微分は、全次数で元の微分への辺付加と右端二面差の符号倍。 -/
lemma serreCubeAppendEdge_d (n : ℕ) (p : ℤ) (x : (serreCubeComplex A n).X p) :
    (serreCubeComplex A (n + 1)).d (p - 1) p
        (serreCubeAppendEdge A n p (p - 1) (by omega) x) =
      serreCubeAppendEdge A n (p + 1) p (by omega)
        ((serreCubeComplex A n).d p (p + 1) x) +
      p.negOnePow • ((serreCubeFace A true n 0).hom.f p x -
        (serreCubeFace A false n 0).hom.f p x) := by
  have h := serreTensorDifferential_apply A (serreCubeComplex A n) (serreInterval A)
    p (p + 1) (-1) 0 (p - 1) p rfl (by omega) (by omega) (by omega) x (serreIntervalEdge A)
  exact h.trans (congrArg (fun z => serreCubeAppendEdge A n (p + 1) p (by omega)
      ((serreCubeComplex A n).d p (p + 1) x) + p.negOnePow • z)
    ((congrArg (fun z => ιTensorObj (serreCubeComplex A n) (serreInterval A) p 0 p (add_zero p)
      (x ⊗ₜ[A] z)) (serreIntervalEdge_d A)).trans
        (serreCubeFace_zero_difference A n p x).symm))

/-- 元の端点面は、任意の斉次元上で元の微分と可換。 -/
lemma serreCubeEndpoint_d (b : Bool) (n : ℕ) (p : ℤ) (x : (serreCubeComplex A n).X p) :
    (serreCubeComplex A (n + 1)).d p (p + 1) ((serreCubeFace A b n 0).hom.f p x) =
      (serreCubeFace A b n 0).hom.f (p + 1) ((serreCubeComplex A n).d p (p + 1) x) :=
  ConcreteCategory.congr_hom ((serreCubeFace A b n 0).hom.comm p (p + 1)) x

end SerrePositivity.KST.SConstruction
