module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassCompatibilityTriangles

/-!
概要：任意の有限切断の実下段逆から、次の段の class 模型逆に使うデータを選ぶ。
方針：元の零底・層逆の段を先に選び、実下段 roof と共通核の係数逆を取る。
規約：下段逆は実データとして受け取り、切断次数と単位 shift を区別する。
使われ方：有限 Postnikov 帰納と、既存の二切断模型の n=1 特殊化。
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

lemma postnikovSuccessor_cutoff_le (n : ℤ) : n ≤ n + 1 := by omega
lemma postnikovSuccessor_nonnegative {n : ℤ} (hn : 0 ≤ n) : 0 ≤ n + 1 := by omega

variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)

structure PostnikovSuccessorClassInverseData (j : ℕ) where
  inverseStage : ℕ
  target_le : j ≤ inverseStage
  inverse : PostnikovZeroLayerInverse R n f j inverseStage target_le
  sourceStage : ℕ
  inverse_le : inverseStage ≤ sourceStage
  baseInverse : NonpositiveInverseRoof R (f.map (postnikovFunctor R n))
    inverseStage sourceStage inverse_le
  layerInverse : PostnikovCommonCore.LayerInverse R hn f baseInverse

lemma exists_postnikovSuccessorClassInverseData_after
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (hₙ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R (n + 1))))
    (lower : ∀ i, ∃ m, ∃ hi : i ≤ m,
      Nonempty (NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi))
    (j bound : ℕ) :
    ∃ d : PostnikovSuccessorClassInverseData R hn f j, bound ≤ d.inverseStage := by
  obtain ⟨i, hj, hb, ⟨e⟩⟩ := exists_postnikovZeroLayerInverse_after R n f hn h₀ hₙ j bound
  obtain ⟨m, hi, ⟨c⟩⟩ := lower i
  obtain ⟨d, _⟩ := PostnikovCommonCore.LayerInverse.exists_after R hn f c h₀ hₙ m
  exact ⟨⟨i, hj, e, m, hi, c, d⟩, hb⟩

namespace PostnikovSuccessorClassInverseData
variable {hn f} {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

abbrev classSource :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueSource R hn f d.baseInverse d.layerInverse

def classProjection : d.classSource R ⟶
    PostnikovCommonCore.postnikovCommonClassBase R hn f d.baseInverse d.layerInverse :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueProjection R hn f d.baseInverse d.layerInverse

lemma classProjection_quasiIso : QuasiIso (d.classProjection R).hom :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueProjection_quasiIso R hn f
    d.baseInverse d.layerInverse

lemma classProjection_surjective (degree : ℤ) :
    Function.Surjective ((d.classProjection R).hom.f degree) :=
  PostnikovCommonCore.postnikovCommonClassStandardGlueProjection_surjective R hn f
    d.baseInverse d.layerInverse degree

def classWitness : Path.Witness R
    (PostnikovCommonCore.postnikovCommonClassStandardGlueLeft R hn f
      d.baseInverse d.layerInverse (hj := d.target_le))
    (PostnikovCommonCore.postnikovCommonClassStandardGlueRight R hn f
      d.baseInverse d.layerInverse (hj := d.target_le)) :=
  PostnikovCommonCore.postnikovCommonClassCompatibilityWitness R hn f
    d.baseInverse d.layerInverse d.inverse

lemma classWitness_projection : (d.classWitness R).hom ≫ Path.map R (SquareZero.projection _ _) =
    d.classProjection R ≫
      Path.diagonal R (PostnikovCommonCore.postnikovCommonClassBase R hn f
        d.baseInverse d.layerInverse) :=
  PostnikovCommonCore.postnikovCommonClassCompatibilityWitness_projection R hn f
    d.baseInverse d.layerInverse d.inverse

end PostnikovSuccessorClassInverseData
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
