module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorInputComponents
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySplitAt

/-!
# 標準二色入力と二つのテンソル冪

HA 3.2.4.7 の自由比較のため、実際の標準パターンの入力を
左右のテンソル冪へ同定する。任意の複体を許し、微分を変えない。
空のブロックも既存の有限テンソル族の分離同型で扱う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
variable {A : Type u} [CommRing A] (X Y : Complex A)

/-- 標準パターンの左ブロックの入力族は一定の X の族。 -/
lemma binaryTensorStandard_left_family (m n : ℕ) :
    (fun i : Fin m => binaryTensorColorObj X Y
      (binaryTensorWordColors (m + n) (binaryTensorStandardPattern m n) (i.castAdd n))) =
        fun _ => X := by
  funext i
  simp [binaryTensorStandardPattern, binaryTensorColorObj]

/-- 標準パターンの右ブロックの入力族は一定の Y の族。 -/
lemma binaryTensorStandard_right_family (m n : ℕ) :
    (fun i : Fin n => binaryTensorColorObj X Y
      (binaryTensorWordColors (m + n) (binaryTensorStandardPattern m n) (i.natAdd m))) =
        fun _ => Y := by
  funext i
  simp [binaryTensorStandardPattern, binaryTensorColorObj]

/-- 実際の標準二色成分から二つのテンソル冪への、微分を保つ指定同型。 -/
def binaryTensorStandardPowersIso (m n : ℕ) :
    binaryTensorWordObj X Y (m + n) (binaryTensorStandardPattern m n) ≅
      power X m ⊗ power Y n :=
  binaryTensorWordFamilyIso X Y (m + n) (binaryTensorStandardPattern m n) ≪≫
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt m n (fun i => binaryTensorColorObj X Y
      (binaryTensorWordColors (m + n) (binaryTensorStandardPattern m n) i)) ≪≫
    tensorIso
      (eqToIso ((congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m) (binaryTensorStandard_left_family X Y m n)).trans
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_const X m)))
      (eqToIso ((congrArg (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n) (binaryTensorStandard_right_family X Y m n)).trans
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_const Y n)))

end SerrePositivity.EInfinity
