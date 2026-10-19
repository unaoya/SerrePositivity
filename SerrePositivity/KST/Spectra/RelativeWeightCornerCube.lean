module

public import SerrePositivity.KST.Spectra.PushoutCubeInterchange
public import SerrePositivity.KST.Spectra.RelativeWeightTensorLatching

/-!
概要：重みの自然変換とパラメーターの射から、相対 latching の交換の実際の立方体を作る。
方針：六つの面の可換性を latching の自然性と tensor の交換則から計算する。
規約：比較先は各段 G_j ⊗ B であり、その射を保つ arrow 同型を構成する。
使われ方：Goerss–Jardine VII §4。相対 pushout-product の latching 表示への接続。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open SerrePositivity.Reedy

namespace SerrePositivity.KST.Spectra.RelativeWeightCornerCube
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {F G : CosimplicialObject SSet.{u}} (θ : F ⟶ G)
  {A B : SSet.{u}} (i : A ⟶ B) (j : SimplexCategory)

/-- A の面の latching の自然性。 -/
lemma faceA : ((latchingEvaluation simplex j).map θ ▷ A) ≫
    ((latchingComparison simplex j).app G ▷ A) =
    ((latchingComparison simplex j).app F ▷ A) ≫ (θ.app j ▷ A) := by
  rw [← comp_whiskerRight, ← comp_whiskerRight, (latchingComparison simplex j).naturality θ]
  rfl

/-- F の面のパラメーターへの自然性。 -/
lemma faceF : ((latchingEvaluation simplex j).obj F ◁ i) ≫
    ((latchingComparison simplex j).app F ▷ B) =
    ((latchingComparison simplex j).app F ▷ A) ≫ (F.obj j ◁ i) :=
  whisker_exchange ((latchingComparison simplex j).app F) i

/-- latching の上面の二変数の交換則。 -/
lemma faceTop : ((latchingEvaluation simplex j).map θ ▷ A) ≫
    ((latchingEvaluation simplex j).obj G ◁ i) =
    ((latchingEvaluation simplex j).obj F ◁ i) ≫
      ((latchingEvaluation simplex j).map θ ▷ B) :=
  (whisker_exchange ((latchingEvaluation simplex j).map θ) i).symm

/-- 相対 latching を先に取る側の標準的な三成分の比較射。 -/
abbrev latchingFirst :=
  PushoutCube.rightDesc (faceA (A := A) θ j) (faceF (F := F) i j) (faceTop θ i j)
    (G.obj j ◁ i) (θ.app j ▷ B) ((latchingComparison simplex j).app G ▷ B)
    (whisker_exchange (θ.app j) i).symm
    (whisker_exchange ((latchingComparison simplex j).app G) i).symm
    (by
      rw [← comp_whiskerRight, ← comp_whiskerRight]
      exact congrArg (fun f ↦ f ▷ B) ((latchingComparison simplex j).naturality θ).symm)

/-- pushout-product を先に取る側の、同じ三成分による比較射。 -/
abbrev productFirst :=
  PushoutCube.leftDesc (faceA (A := A) θ j) (faceF (F := F) i j) (faceTop θ i j)
    (G.obj j ◁ i) (θ.app j ▷ B) ((latchingComparison simplex j).app G ▷ B)
    (whisker_exchange (θ.app j) i).symm
    (whisker_exchange ((latchingComparison simplex j).app G) i).symm
    (by
      rw [← comp_whiskerRight, ← comp_whiskerRight]
      exact congrArg (fun f ↦ f ▷ B) ((latchingComparison simplex j).naturality θ).symm)

/-- 重みとパラメーターの実際の立方体から得られる、比較射を保つ交換同型。 -/
def arrowIso : Arrow.mk (latchingFirst θ i j) ≅ Arrow.mk (productFirst θ i j) :=
  PushoutCube.interchangeArrowIso _ _ _ _ _ _ _ _ _

end
end SerrePositivity.KST.Spectra.RelativeWeightCornerCube
