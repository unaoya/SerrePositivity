module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.EndDifferential

/-!
概要：実正規化 bar 上の末尾付加作用素の微分を、二つの theta 合成へ帰着する。
方針：内部微分の消滅と次数 −1 の MC 自己 Hom 微分公式を使う。
規約：縮約恒等式の右辺との一致は後続の列計算で示す。
使われ方：有限 support 上の局所縮約。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] (F : J ⥤ ModuleCategory R D)

local notation "B" => ForgetEnrichment.to (Complex R)
  (dgCoherentBarNormalizedGraded R D (dgCoherentBarStrictDiagram R D F))
local notation "P" => dgCoherentBarStrictNormalizedModule R D F
local notation "T" => dgCoherentBarNormalizedTheta R D (dgCoherentBarStrictDiagram R D F)

lemma dgStrictAppendHom_d (b : J) :
    (moduleHom R D P P).d (-1) 0 (dgStrictAppendHom R D F b) =
      dgStrictNormalizedEndRebase R D F 0
        (compose R (x := B) (y := B) (z := B) T (dgStrictAppendGradedHom R D F b)
          (show (-1 : ℤ) + 1 = 0 by omega) +
        compose R (x := B) (y := B) (z := B) (dgStrictAppendGradedHom R D F b) T
          (show (1 : ℤ) + -1 = 0 by omega)) := by
  have he : dgStrictNormalizedEndDifferential R D F (-1) (dgStrictAppendGradedHom R D F b) =
      compose R (x := B) (y := B) (z := B) T (dgStrictAppendGradedHom R D F b)
        (show (-1 : ℤ) + 1 = 0 by omega) +
      compose R (x := B) (y := B) (z := B) (dgStrictAppendGradedHom R D F b) T
        (show (1 : ℤ) + -1 = 0 by omega) := by
    unfold dgStrictNormalizedEndDifferential
    erw [dgStrictAppendGradedHom_d R D F b]
    simp only [neg_add_cancel, Int.negOnePow_zero, one_smul, zero_add]
  have hd := dgStrictNormalizedEndRebase_d R D F (-1) (dgStrictAppendGradedHom R D F b)
  exact hd.trans (congrArg (dgStrictNormalizedEndRebase R D F 0) he)

end SerrePositivity.InfinityCategories
