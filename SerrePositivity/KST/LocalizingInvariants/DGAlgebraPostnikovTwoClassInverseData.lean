module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassCompatibilityTriangles
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovOneNonpositiveInverseRoof

/-!
概要：元の π₀・π₁・π₂ pro 同型から、二切断逆に使う底 roof・係数逆・class 整合を選ぶ。
方針：先に零層逆の源段を選び、その段を対象とする τ₁ roof と共通係数逆を構成する。
規約：実二切断代数の逆そのものは未主張。使われ方：class 模型での逆の持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

/-- 元の低い段 j の class へ整合する、細分した一切断 roof と係数逆の実データ。 -/
structure PostnikovTwoClassInverseData (j : ℕ) where
  inverseStage : ℕ
  target_le : j ≤ inverseStage
  inverse : PostnikovZeroLayerInverse R 1 f j inverseStage target_le
  sourceStage : ℕ
  inverse_le : inverseStage ≤ sourceStage
  baseInverse : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1))
    inverseStage sourceStage inverse_le
  layerInverse : PostnikovCommonLayerInverse R f baseInverse

/-- 任意に指定した段より後に、追加の class 整合仮定なしに実データを選べる。 -/
lemma exists_postnikovTwoClassInverseData_after
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (h₁ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1)))
    (h₂ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 2))) (j bound : ℕ) :
    ∃ d : PostnikovTwoClassInverseData R f j, bound ≤ d.inverseStage := by
  obtain ⟨i, hj, hb, ⟨e⟩⟩ := exists_postnikovZeroLayerInverse_after R 1 f (by omega) h₀ h₂ j bound
  obtain ⟨m, hi, ⟨c⟩⟩ := postnikovOneMap_exists_nonpositiveInverseRoof R f h₀ h₁ i
  exact ⟨⟨i, hj, e, m, hi, c, postnikovCommonLayerInverse R f c h₀ h₂⟩, hb⟩

namespace PostnikovTwoClassInverseData
variable {f} {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

abbrev classSource :=
  postnikovCommonClassStandardGlueSource R f d.baseInverse d.layerInverse

def classProjection : d.classSource R ⟶ postnikovCommonClassBase R f d.baseInverse d.layerInverse :=
  postnikovCommonClassStandardGlueProjection R f d.baseInverse d.layerInverse

lemma classProjection_quasiIso : QuasiIso (d.classProjection R).hom :=
  postnikovCommonClassStandardGlueProjection_quasiIso R f d.baseInverse d.layerInverse

lemma classProjection_surjective (n : ℤ) : Function.Surjective ((d.classProjection R).hom.f n) :=
  postnikovCommonClassStandardGlueProjection_surjective R f d.baseInverse d.layerInverse n

/-- 元の候補係数逆の class 像から、Aⱼ の元の標準 class への実乗法的経路。 -/
def classWitness : Path.Witness R
    (postnikovCommonClassStandardGlueLeft R f d.baseInverse d.layerInverse (hj := d.target_le))
    (postnikovCommonClassStandardGlueRight R f d.baseInverse d.layerInverse (hj := d.target_le)) :=
  postnikovCommonClassCompatibilityWitness R f d.baseInverse d.layerInverse d.inverse

lemma classWitness_projection : (d.classWitness R).hom ≫ Path.map R (SquareZero.projection _ _) =
    d.classProjection R ≫
      Path.diagonal R (postnikovCommonClassBase R f d.baseInverse d.layerInverse) :=
  postnikovCommonClassCompatibilityWitness_projection R f d.baseInverse d.layerInverse d.inverse

end PostnikovTwoClassInverseData
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
