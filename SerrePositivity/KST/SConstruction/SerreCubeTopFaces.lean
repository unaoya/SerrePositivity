module
public import SerrePositivity.KST.SConstruction.SerreCubeTopCell
public import SerrePositivity.KST.SConstruction.SerreCubeCoordinateValues
public import SerrePositivity.DifferentialGraded.Complexes.RightUnitorEvaluation
public import SerrePositivity.DifferentialGraded.Complexes.MapEvaluation

/-! # 元の Serre 立方体の面の斉次生成元での値
概要：元の右端の面は端点の tensor、内側の面は一段小さい同じ面の tensor である。
方針：元の面の chain map の式と、元の tensor・右単位射の斉次評価を使う。
規約：元の右端からの座標順を保持。使われ方：最高生成元の全面境界式。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

/-- 元の右端の面は、任意の元の斉次元と同じ端点の tensor。 -/
lemma serreCubeFace_zero_apply (b : Bool) (n : ℕ) (k : ℤ)
    (x : (serreCubeComplex A n).X k) :
    (serreCubeFace A b n 0).hom.f k x =
      ιTensorObj (serreCubeComplex A n) (serreInterval A) k 0 k (add_zero k)
        (x ⊗ₜ[A] (cycleFromUnit _ (serreIntervalEndpointComonHom A b).hom).val) := by
  have h (P Q : Complex A) (f : 𝟙_ (Complex A) ⟶ Q) (k : ℤ) (x : P.X k) :
      ((ρ_ P).inv ≫ (𝟙 P ⊗ₘ f)).f k x =
        ιTensorObj P Q k 0 k (add_zero k) (x ⊗ₜ[A] (cycleFromUnit Q f).val) := by
    rw [chain_comp_apply, complexRightUnitor_inv_apply, tensorMap_apply]
    rfl
  exact (congrArg (fun f => f.f k x) (serreCubeFace_zero_hom A b n)).trans
    (h (serreCubeComplex A n) (serreInterval A) (serreIntervalEndpointComonHom A b).hom k x)

/-- 元の内側の面は、全斉次純粋 tensor 上で同じ一段小さい面の作用を回収する。 -/
lemma serreCubeFace_succ_apply (b : Bool) (n : ℕ) (i : Fin (n + 1))
    (p q k : ℤ) (hk : p + q = k)
    (x : (serreCubeComplex A n).X p) (y : (serreInterval A).X q) :
    (serreCubeFace A b (n + 1) i.succ).hom.f k
        (ιTensorObj (serreCubeComplex A n) (serreInterval A) p q k hk (x ⊗ₜ[A] y)) =
      ιTensorObj (serreCubeComplex A (n + 1)) (serreInterval A) p q k hk
        ((serreCubeFace A b n i).hom.f p x ⊗ₜ[A] y) :=
  (congrArg (fun f => f.f k
    (ιTensorObj (serreCubeComplex A n) (serreInterval A) p q k hk (x ⊗ₜ[A] y)))
    (serreCubeFace_succ_hom A b n i)).trans
      (tensorMap_apply (serreCubeFace A b n i).hom (𝟙 (serreInterval A)) p q k hk x y)

/-- 元の右端の二面の最高生成元の像の差は、元の辺の境界との tensor。 -/
lemma serreCubeTopCell_face_zero_difference (n : ℕ) :
    (serreCubeFace A true n 0).hom.f (-(n : ℤ)) (serreCubeTopCell A n) -
        (serreCubeFace A false n 0).hom.f (-(n : ℤ)) (serreCubeTopCell A n) =
      ιTensorObj (serreCubeComplex A n) (serreInterval A)
        (-(n : ℤ)) 0 (-(n : ℤ)) (by omega)
          (serreCubeTopCell A n ⊗ₜ[A]
            ((cycleFromUnit _ (serreIntervalOne A)).val -
              (cycleFromUnit _ (serreIntervalZero A)).val)) := by
  have h := congrArg₂ (fun x y => x - y)
    (serreCubeFace_zero_apply A true n (-(n : ℤ)) (serreCubeTopCell A n))
    (serreCubeFace_zero_apply A false n (-(n : ℤ)) (serreCubeTopCell A n))
  exact h.trans (by
    simp only [TensorProduct.tmul_sub, map_sub]
    rfl)

end SerrePositivity.KST.SConstruction
