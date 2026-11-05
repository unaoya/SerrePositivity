module
public import SerrePositivity.InfinityCategories.F1.LeftFibrationInitialNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationPointHomFamily
/-!
概要：固定終点の fiber の比較から、指定頂点の選択済み標準 Hom の族の同値性を反映する。
方針：中間空間の底側の二射影の同値を消去し、終点評価との可換性を使う。
規約：元の頂点の始対象性は仮定しない。終点ごとの同値だけを入力にする。
使われ方：固定終点の bar Hom 比較から標準 native 余錐の普遍性を結論する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
attribute [local instance] vertexFiber_kanComplex_of_leftFibration

lemma dgCoherentBarPointHomFamily_equivalence_of_fiberComparison
    {E F B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] (q : F ⟶ B) [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (d : E _⦋0⦌) (d' : F _⦋0⦌)
    (hd : f.app (Opposite.op ⦋0⦌) d = d') (hd' : IsInitialVertex d')
    (y : B _⦋0⦌) (hFiber : IsQCatEquivalence (vertexFiberMap p q f hf y)) :
    IsSimplicialHomotopyEquivalence (HomotopyLimits.leftFibrationPointHomFamily p d y) := by
  let M := leftFibrationInitialTotalMap p q f hf d d' hd y
  let eBase := eqToIso (congrArg
    (fun t : (Δ[0] : SSet.{u}) ⟶ B => vertexFiber (sliceUnderProjection t) y)
    (leftFibrationInitialBaseDiagram_eq p q f hf d d' hd).symm)
  have hProjection : IsQCatEquivalence
      (leftFibrationInitialProjection q d' y ≫ eBase.hom) :=
    (isQCatEquivalence_of_trivialKanFibration (leftFibrationInitialProjection q d' y)).comp
      (qCatEquivalenceOfIso eBase).isQCatEquivalence
  have hSquare : M ≫ (leftFibrationInitialProjection q d' y ≫ eBase.hom) =
      leftFibrationInitialProjection p d y :=
    leftFibrationInitialTotalMap_projection p q f hf d d' hd y
  have hComposite : IsQCatEquivalence
      (M ≫ (leftFibrationInitialProjection q d' y ≫ eBase.hom)) := by
    rw [hSquare]
    exact isQCatEquivalence_of_trivialKanFibration (leftFibrationInitialProjection p d y)
  have hM : IsQCatEquivalence M := hProjection.cancel_right hComposite
  let : TrivialKanFibration (leftFibrationInitialEvaluation q d' y) :=
    leftFibrationInitialEvaluation_trivialKanFibration q d' hd' y
  have hEvaluation := isQCatEquivalence_of_trivialKanFibration
    (leftFibrationInitialEvaluation q d' y)
  have hTransfer := hM.comp hEvaluation
  rw [leftFibrationInitialTotalMap_evaluation] at hTransfer
  have hSourceEvaluation : IsQCatEquivalence (leftFibrationInitialEvaluation p d y) :=
    hFiber.cancel_right hTransfer
  change IsSimplicialHomotopyEquivalence
    (HomotopyLimits.leftFibrationPointHomLift p d y ≫ leftFibrationInitialEvaluation p d y)
  exact (HomotopyLimits.leftFibrationPointHomLift_homotopyEquivalence p d y).comp
    hSourceEvaluation.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories
