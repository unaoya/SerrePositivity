module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaSmash
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneCohomotopy
public import SerrePositivity.EInfinity.HomologyZero.Classes
public import SerrePositivity.KST.Spectra.SphereSimplex

/-!
# シフトした単位の Γ の基本円

DAG XIII §2.2 のスペクトル構造射への前段。指定された π/H 比較の下で
単位の類に対応する一つの代表を選ぶ。複体変数には選択を行わない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
variable (A : Type u) [CommRing A]

/-- 同じ Γ の第 r 段の零基点は、単体的加群の零元そのものである。 -/
lemma levelPointed_basepoint (M : Complex A) (r : ℕ) :
    ((levelPointedFunctor A r).obj M).basepoint =
      (0 : ((levelModuleFunctor A r).obj M).obj
        (Opposite.op (SimplexCategory.mk 0))) := rfl

instance levelPointedKan (M : Complex A) (r : ℕ) :
    SSet.KanComplex (((levelPointedFunctor A r).obj M).right) := by
  change SSet.KanComplex ((levelSpaceFunctor A r).obj M)
  infer_instance

/-- 第 1 段の π₁ で、指定比較が単位の H⁰ の類へ送る元。 -/
def unitCircleClass :
    KanHomotopyGroup ((levelSpaceFunctor A 1).obj (𝟙_ (Complex A))) 0
      (0 : ((levelModuleFunctor A 1).obj (𝟙_ (Complex A))).obj
        (Opposite.op (SimplexCategory.mk 0))) :=
  (levelPiCohomologyEquivAt A (𝟙_ (Complex A)) 0 1 0 (by decide)).symm
    (Multiplicative.ofAdd (HomologyZero.unitClass (𝟙_ (Complex A)) (𝟙 _)))

/-- 複体変数によらず一度だけ選ぶ基本円の代表。 -/
def unitCircle : PointedSimplicialSet.circle.{u} ⟶
    (levelPointedFunctor A 1).obj (𝟙_ (Complex A)) :=
  (KST.Spectra.SphereSimplex.equiv _ 1).symm (Quotient.out (unitCircleClass A))

/-- 選んだ円の類は、指定された基本類である。 -/
lemma unitCircle_class :
    KanHomotopyGroup.mk
      (KST.Spectra.SphereSimplex.equiv _ 1 (unitCircle A)) = unitCircleClass A := by
  rw [unitCircle, Equiv.apply_symm_apply]
  exact Quotient.out_eq _

/-- 同じ π/H 比較で基本円の像を計算する。 -/
lemma unitCircle_homology :
    levelPiCohomologyEquivAt A (𝟙_ (Complex A)) 0 1 0 (by decide)
      (unitCircleClass A) =
    Multiplicative.ofAdd (HomologyZero.unitClass (𝟙_ (Complex A)) (𝟙 _)) :=
  (levelPiCohomologyEquivAt A (𝟙_ (Complex A)) 0 1 0 (by decide)).apply_symm_apply _

end SerrePositivity.EInfinity.PowerOperation
