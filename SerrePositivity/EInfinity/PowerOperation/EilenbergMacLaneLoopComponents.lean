module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaCohomotopy
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneLoopProperties
public import SerrePositivity.KST.Spectra.LoopHomotopyNaturality

/-!
# loop Γ(M[1]) の連結成分と H⁰(M) の自然な比較

DAG XIII §2.2 の零次数の Ω 比較への前段。指定 loop 比較・正規化余単位・
元のシフトのホモロジー同型を、その自然性とともに合成する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open SerrePositivity.KST.Spectra
  (loopZeroHomotopyEquiv loopHomotopyEquiv_natural pointedHomotopyMap)
variable (A : Type u) [CommRing A]

/-- 乗法記法の型から元の加法記法の台へ戻す同値。 -/
def multiplicativeForgetEquiv (B : Type u) : Multiplicative B ≃ B where
  toFun := Multiplicative.toAdd
  invFun := Multiplicative.ofAdd
  left_inv _ := rfl
  right_inv _ := rfl

/-- 同じ loop Γ の零次数を元の複体の H⁰ で表示する。 -/
def gammaLoopPiZeroCohomologyEquiv (M : Complex A) :
    KanHomotopy ((gammaLoopFunctor A).obj M).right 0
      ((gammaLoopFunctor A).obj M).basepoint ≃ M.homology 0 :=
  (loopZeroHomotopyEquiv (gammaPointed A (M⟦(1 : ℤ)⟧))).trans
    ((gammaPiCohomologyEquiv A (M⟦(1 : ℤ)⟧) 0).toEquiv.trans
      ((multiplicativeForgetEquiv _).trans
        ((((homologyFunctor (ModuleCat A) (.up ℤ) 0).shiftIso
          (1 : ℤ) (-1 : ℤ) (0 : ℤ) (by decide)).app M).toLinearEquiv.toEquiv)))

lemma gammaLoopPiZeroCohomologyEquiv_naturality {M N : Complex A} (f : M ⟶ N)
    (a : KanHomotopy ((gammaLoopFunctor A).obj M).right 0
      ((gammaLoopFunctor A).obj M).basepoint) :
    gammaLoopPiZeroCohomologyEquiv A N
      (pointedHomotopyMap 0 ((gammaLoopFunctor A).map f) a) =
      (homologyMap f 0).hom (gammaLoopPiZeroCohomologyEquiv A M a) := by
  let sh := (homologyFunctor (ModuleCat A) (.up ℤ) 0).shiftIso
    (1 : ℤ) (-1 : ℤ) (0 : ℤ) (by decide)
  have hl := loopHomotopyEquiv_natural ((gammaPointedFunctor A).map (f⟦(1 : ℤ)⟧')) 0 a
  have hπ := gammaPiCohomologyEquiv_naturality A (f⟦(1 : ℤ)⟧') 0
    (loopZeroHomotopyEquiv (gammaPointed A (M⟦(1 : ℤ)⟧)) a)
  have h₁ := (congrArg (fun t => (sh.app N).hom.hom
    (Multiplicative.toAdd (gammaPiCohomologyEquiv A (N⟦(1 : ℤ)⟧) 0 t))) hl).trans
      (congrArg (fun t => (sh.app N).hom.hom (Multiplicative.toAdd t)) hπ)
  have h₂ := congrArg (fun k => k.hom (Multiplicative.toAdd
    (gammaPiCohomologyEquiv A (M⟦(1 : ℤ)⟧) 0
      (loopZeroHomotopyEquiv (gammaPointed A (M⟦(1 : ℤ)⟧)) a)))) (sh.hom.naturality f)
  exact h₁.trans h₂

end SerrePositivity.EInfinity.PowerOperation
