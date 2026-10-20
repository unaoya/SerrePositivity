module

public import SerrePositivity.EInfinity.Hammock.LengthZero
public import SerrePositivity.EInfinity.Hammock.WeakStageSuccessor

/-!
# proper 図式の元の全有限長さ段階の弱同値

概要：proper 図式間の成分ごとの弱同値は、全有限段階の元の比較を弱同値にする。
方針：長さ零の元の同型を基底にし、元の次段階の pushout 比較で帰納する。
規約：段階や成分の Kan 性を追加仮定にしない。
使われ方：長さ濾過の filtered 余極限による proper 余極限の比較。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory
open SerrePositivity.InfinityCategories

variable {F G : Word ⥤ SSet.{w}} (η : F ⟶ G)

lemma weakLengthStageMap_zero (hη : IsWeakHomotopyEquivalence (η.app Word.empty)) :
    IsWeakHomotopyEquivalence (lengthStageMap η 0) := by
  have hF := (isPrecompositionEquivalence_of_iso (lengthZeroIso F).symm)
  have hG := (isPrecompositionEquivalence_of_iso (lengthZeroIso G).symm)
  apply hF.isWeakHomotopyEquivalence.cancel_left
  change IsWeakHomotopyEquivalence
    (lengthStageInclusion F 0 Word.empty (le_refl 0) ≫ lengthStageMap η 0)
  rw [lengthStageInclusion_map]
  exact hη.comp hG.isWeakHomotopyEquivalence

lemma weakLengthStageMap (hF : ProperDiagram F) (hG : ProperDiagram G)
    (hη : ∀ a, IsWeakHomotopyEquivalence (η.app a)) (n : ℕ) :
    IsWeakHomotopyEquivalence (lengthStageMap η n) := by
  induction n with
  | zero => exact weakLengthStageMap_zero η (hη Word.empty)
  | succ n ih => exact weakLengthStageMap_succ η hF hG hη n ih

end SerrePositivity.EInfinity.Hammock
