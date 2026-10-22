module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonZeroCoefficient

/-!
概要：元の群の pro 同型と選んだ一切断 roof から、共通零底上の実係数逆を選ぶ。
方針：同じ実代数逆の底と係数を取り、元の roof との底の一致を証明して制限する。
規約：底の一致や作用保存を追加仮定にしない。使われ方：元の共通底上の係数逆。
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
variable (R : Type u) [CommRing R] (n : ℤ) {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)

structure PostnikovCommonZeroInverse where
  inverseStage : ℕ
  inverse_le : i ≤ inverseStage
  inverse : PostnikovZeroLayerInverse R n f i inverseStage inverse_le
  stage : ℕ
  source_le : m ≤ stage
  stage_le : inverseStage ≤ stage
  base_eq : postnikovOneRoofZeroNumerator R f (postnikovOneRoofRefine R f c source_le) =
    postnikovOneRoofZeroDenominator R f (postnikovOneRoofRefine R f c source_le) ≫
      postnikovMap R (B.transition stage_le).hom 0 ≫ inverse.base
  coefficient : postnikovCommonZeroDenominatorLayer R n f
      (postnikovOneRoofRefine R f c source_le) ⟶
    postnikovCommonZeroNumeratorLayer R n f (postnikovOneRoofRefine R f c source_le)
  coefficient_hom : coefficient.hom =
    postnikovLayerMap R (B.transition stage_le).hom n ≫ inverse.coefficient.hom
  left_coefficient : postnikovLayerMap R (f.app stage).hom n ≫ coefficient.hom =
    postnikovLayerMap R (A.transition (inverse_le.trans stage_le)).hom n
  right_coefficient : coefficient.hom ≫ postnikovLayerMap R (f.app i).hom n =
    postnikovLayerMap R (B.transition (inverse_le.trans stage_le)).hom n

namespace PostnikovCommonZeroInverse

def ofInverse (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    {l : ℕ} {hj : i ≤ l} (e : PostnikovZeroLayerInverse R n f i l hj) :
    PostnikovCommonZeroInverse R n f c := by
  let h := postnikovZeroLayerInverse_common_zero_base R f c h₀ e
  let k := h.choose
  let hm : m ≤ k := h.choose_spec.choose
  let hl : l ≤ k := h.choose_spec.choose_spec.choose
  have hb : postnikovOneRoofZeroNumerator R f (postnikovOneRoofRefine R f c hm) =
      postnikovOneRoofZeroDenominator R f (postnikovOneRoofRefine R f c hm) ≫
        postnikovMap R (B.transition hl).hom 0 ≫ e.base := h.choose_spec.choose_spec.choose_spec
  exact
    { inverseStage := l
      inverse_le := hj
      inverse := e
      stage := k
      source_le := hm
      stage_le := hl
      base_eq := hb
      coefficient := postnikovCommonZeroCoefficientMap R n f c e hm hl hb
      coefficient_hom := postnikovCommonZeroCoefficientMap_hom R n f c e hm hl hb
      left_coefficient := postnikovCommonZeroCoefficientMap_left R n f c e hm hl hb
      right_coefficient := postnikovCommonZeroCoefficientMap_right R n f c e hm hl hb }

end PostnikovCommonZeroInverse

def postnikovCommonZeroInverse (hn : 0 ≤ n)
    (h₀ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 0)))
    (hₙ : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R (n + 1)))) :
    PostnikovCommonZeroInverse R n f c := by
  let h := exists_postnikovZeroLayerInverse_after R n f hn h₀ hₙ i m
  let l := h.choose
  let hj : i ≤ l := h.choose_spec.choose
  let e : PostnikovZeroLayerInverse R n f i l hj := h.choose_spec.choose_spec.2.some
  exact PostnikovCommonZeroInverse.ofInverse R n f c h₀ e

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
