module

public import SerrePositivity.EInfinity.PowerOperation.CyclicOrbitModel

/-!
# 同じ orbit 解像度の項と指定微分

DAG XIII Construction 2.2.6 の周期 Hom 比較の補助。
負の次数への実零延長の項を元の正則係数に戻し、指定微分を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
variable (p : ℕ) [NeZero p] (k : Type u) [CommRing k]

/-- 負の次数にある同じ正則係数への指定同型。 -/
def cyclicOrbitResolutionXIso (s : ℕ) :
    (cyclicOrbitResolution p k).X (-(s : ℤ)) ≅
      Rep.leftRegular k (PowerOperationCyclicGroup.{u} p) :=
  (cyclicOrbitProjectiveResolution p k).complex.extendXIso
    ComplexShape.embeddingDownNat
    (show ComplexShape.embeddingDownNat.f s = -(s : ℤ) from rfl)

/-- 同じ零延長の微分は、元の解像度の微分を保つ。 -/
lemma cyclicOrbitResolution_d_coordinates (s : ℕ) :
    (cyclicOrbitResolution p k).d (-((s + 1 : ℕ) : ℤ)) (-(s : ℤ)) ≫
      (cyclicOrbitResolutionXIso p k s).hom =
    (cyclicOrbitResolutionXIso p k (s + 1)).hom ≫
      (cyclicOrbitProjectiveResolution p k).complex.d (s + 1) s := by
  dsimp only [cyclicOrbitResolution, cyclicOrbitResolutionXIso]
  rw [extend_d_eq _ _ (i := s + 1) (j := s)
    (show ComplexShape.embeddingDownNat.f (s + 1) = -((s + 1 : ℕ) : ℤ) from rfl)
    (show ComplexShape.embeddingDownNat.f s = -(s : ℤ) from rfl)]
  simp only [Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- 同じ鎖解像度の微分は、偶数の鎖次数でノルム、奇数で逆生成元の差。 -/
lemma cyclicOrbitProjectiveResolution_d (s : ℕ) :
    (cyclicOrbitProjectiveResolution p k).complex.d (s + 1) s =
    if Even (s + 1) then
      (Rep.leftRegular k (PowerOperationCyclicGroup.{u} p)).norm.asHom
    else
      (Rep.leftRegular k (PowerOperationCyclicGroup.{u} p)).applyAsHom
        (powerOperationCyclicGenerator p)⁻¹ - 𝟙 _ := by
  simp [cyclicOrbitProjectiveResolution, Rep.FiniteCyclicGroup.resolution,
    Rep.FiniteCyclicGroup.chainComplexFunctor, HomologicalComplex.alternatingConst]

end SerrePositivity.EInfinity.PowerOperation
