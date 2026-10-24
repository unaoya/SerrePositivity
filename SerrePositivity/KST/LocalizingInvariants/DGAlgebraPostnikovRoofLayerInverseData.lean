module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRoofLayerCoefficient

/-!
概要：原仮定から任意の有限段の共通零底・層逆・後続細分を選ぶ。
方針：元の π₀ と πₙ₊₁ の pro 逆を同じ細分へ揃え、既存の実双加群比較へ渡す。
規約：作用保存や class 整合を追加入力しない。使われ方：高次有限段の帰納データ。
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
variable (R : Type u) [CommRing R] (n : ℤ) (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R n)) i m hi)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

structure PostnikovRoofLayerInverseData where
  inverseStage : ℕ
  target_le : i ≤ inverseStage
  inverse : PostnikovZeroLayerInverse R n f i inverseStage target_le
  stage : ℕ
  source_le : m ≤ stage
  inverse_le : inverseStage ≤ stage
  base_eq : PostnikovRoofZeroSpan.numerator R n hn f (c.refine R source_le) =
    PostnikovRoofZeroSpan.denominator R n hn f (c.refine R source_le) ≫
      postnikovMap R (B.transition inverse_le).hom 0 ≫ inverse.base

lemma exists_postnikovRoofLayerInverseData_after
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (hₙ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R (n + 1)))) (bound : ℕ) :
    ∃ d : PostnikovRoofLayerInverseData R n hn f c, bound ≤ d.stage := by
  obtain ⟨l, hj, hb, ⟨e⟩⟩ := exists_postnikovZeroLayerInverse_after R n f hn h₀ hₙ i bound
  obtain ⟨k, hm, hl, he⟩ := PostnikovRoofZeroSpan.common_zero_base R n hn f c h₀ e
  exact ⟨⟨l, hj, e, k, hm, hl, he⟩, hb.trans hl⟩

namespace PostnikovRoofLayerInverseData
variable (d : PostnikovRoofLayerInverseData R n hn f c)

def coefficient :
    bimoduleRestrict (c.refine R d.source_le).roof.denominator
      (postnikovLayerBaseBimodule R (B.obj d.stage).obj n hn) ⟶
    bimoduleRestrict (c.refine R d.source_le).roof.numerator
      (postnikovLayerBaseBimodule R (A.obj i).obj n hn) :=
  PostnikovRoofZeroSpan.coefficient R n hn f c d.inverse d.source_le d.inverse_le d.base_eq

lemma coefficient_left : postnikovLayerMap R (f.app d.stage).hom n ≫
    (d.coefficient R n hn f c).hom =
      postnikovLayerMap R (A.transition (d.target_le.trans d.inverse_le)).hom n :=
  PostnikovRoofZeroSpan.coefficient_left R n hn f c d.inverse d.source_le d.inverse_le d.base_eq

lemma coefficient_right : (d.coefficient R n hn f c).hom ≫ postnikovLayerMap R (f.app i).hom n =
    postnikovLayerMap R (B.transition (d.target_le.trans d.inverse_le)).hom n :=
  PostnikovRoofZeroSpan.coefficient_right R n hn f c d.inverse d.source_le d.inverse_le d.base_eq

end PostnikovRoofLayerInverseData
end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
