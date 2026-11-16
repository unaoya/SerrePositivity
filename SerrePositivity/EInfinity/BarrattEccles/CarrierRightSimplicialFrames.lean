module

public import SerrePositivity.EInfinity.BarrattEccles.RightSimplicialFrames
public import SerrePositivity.EInfinity.BarrattEccles.CarrierRightFrames
public import SerrePositivity.EInfinity.BarrattEccles.CarrierDiagramModel

/-!
# 元の右 frame の底の単体的表示

概要：BM 命題 4.1・Hovey §5.2 の元の右 frame を底の複体射で表示する。
方針：元の単体的右 frame と比較自然変換を同じ忘却で送る。
規約：元の frame とその全成分を保持する。
使われ方：底の始域 frame との混合 Hom の比較。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy

variable (A : Type u) [CommRing A]

/-- 概要：同じ右 frame の底の単体的な族（Hovey §5.2）。
方針：元の単体的右 frame に忘却を後合成する。
規約：元の代数射と全次元を保持する。
使われ方：底の混合 Hom の終域。 -/
def carrierRightSimplicialFrameFamily :
    (operad A).Algebra ⥤ SimplexCategoryᵒᵖ ⥤ Complex A :=
  rightSimplicialFrameFamily A ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj (Operad.Algebra.forget (operad A))
/-- 概要：元の複体から底の右 frame への自然な比較（Hovey §5.2）。
方針：元の augmentation を全単体で忘却する。
規約：元の代数にも単体作用素にも自然。
使われ方：底の混合 Hom の左比較。 -/
def carrierRightSimplicialFrameAugmentation :
    Operad.Algebra.forget (operad A) ⋙ Functor.const SimplexCategoryᵒᵖ ⟶
      carrierRightSimplicialFrameFamily A :=
  Functor.whiskerRight (rightSimplicialFrameAugmentation A)
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ _ _).obj (Operad.Algebra.forget (operad A)))
/-- 概要：底の単体的右 frame への比較は擬同型（Hovey §5.2）。
方針：同じ元の右 frame 比較の擬同型性を使う。
規約：全次元で同じ複体射を使う。
使われ方：混合 Hom の比較の反転。 -/
lemma carrierRightSimplicialFrameAugmentation_quasiIso (X : (operad A).Algebra)
    (n : SimplexCategoryᵒᵖ) :
    QuasiIso (((carrierRightSimplicialFrameAugmentation A).app X).app n) :=
  rightFrameComparison_quasiIso A X n.unop
/-- 概要：底の単体的右 frame の値は fibrant（Hovey §5.2）。
方針：具体的な複体モデルの全対象の fibrancy を使う。
規約：元の対象に cofibrancy は要求しない。
使われ方：混合 Hom の左比較の条件。 -/
lemma carrierRightSimplicialFrame_fibrant (X : (operad A).Algebra)
    (n : SimplexCategoryᵒᵖ) :
    let := projectiveModelCategory A
    IsFibrant (((carrierRightSimplicialFrameFamily A).obj X).obj n) := by
  let := projectiveModelCategory A
  exact CarrierDiagram.complex_isFibrant A _
/-- 概要：底の単体的右 frame の反対は Reedy cofibrant（Hovey §5.2）。
方針：同じ底の右 frame の証明を使う。
規約：frame を選び直さない。
使われ方：混合 Hom の右比較の条件。 -/
lemma carrierRightSimplicialFrame_cofibrant (X : (operad A).Algebra) :
    let := projectiveModelCategory A
    reedyLeft simplex (cofibrations (Complex A)ᵒᵖ)
      (initial.to ((carrierRightSimplicialFrameFamily A).obj X).rightOp) := by
  let := projectiveModelCategory A
  exact carrierRightFrame_cofibrant A X
/-- 概要：底の単体的右 frame の反対はホモトピー定値（Hovey §5.2）。
方針：同じ底の余単体的右 frame の全作用素の証明を使う。
規約：任意の次元と単体作用素。
使われ方：底の右 Hom 図式の Kan 性。 -/
lemma carrierRightSimplicialFrame_homotopicallyConstant (X : (operad A).Algebra)
    {n m : SimplexCategory} (f : n ⟶ m) :
    let := projectiveModelCategory A
    weakEquivalences (Complex A)ᵒᵖ
      (((carrierRightSimplicialFrameFamily A).obj X).rightOp.map f) := by
  let := projectiveModelCategory A
  exact carrierRightFrame_homotopicallyConstant A X f

end SerrePositivity.EInfinity.BarrattEccles
