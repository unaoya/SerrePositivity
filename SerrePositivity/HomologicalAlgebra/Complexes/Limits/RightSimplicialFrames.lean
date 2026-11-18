module

public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.RightFrames
public import SerrePositivity.EInfinity.BarrattEccles.CarrierDiagramModel

/-!
# 元の 複体圏での単体的右 frame の族

概要：BM 命題 4.1・Hovey §5 の右 frame を元の複体の射で表示する。
方針：反対圏の余単体的 frame と augmentation を同時に反転する。
規約：新しい frame を選ばず、既存の右 frame の全成分を保持する。
使われ方：混合 Hom の両側比較を具体的な 複体の小図式へ適用する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.ComplexLimits

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomotopicalAlgebra _root_.Opposite
open _root_.SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.Reedy

variable (A : Type u) [CommRing A]

/-- 概要：既存の右 frame を元の複体圏の単体図式にする（Hovey §5.2）。
方針：各自然変換も leftOp で反転する。
規約：すべての元の複体射に共変。
使われ方：小図式全体に自然な混合 Hom の終域。 -/
def rightSimplicialFrameFamily : (Complex A) ⥤ SimplexCategoryᵒᵖ ⥤ (Complex A) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact
    { obj := fun X => (_root_.SerrePositivity.ComplexLimits.rightFrame A X).leftOp
      map := fun f => NatTrans.leftOp ((_root_.SerrePositivity.ComplexLimits.rightFrameFamily A).obj.map f.op)
      map_id := by
        intro X
        apply NatTrans.ext
        funext n
        change (((_root_.SerrePositivity.ComplexLimits.rightFrameFamily A).obj.map (𝟙 (op X))).app n.unop).unop = 𝟙 _
        rw [(_root_.SerrePositivity.ComplexLimits.rightFrameFamily A).obj.map_id]
        rfl
      map_comp := by
        intro X Y Z f g
        apply NatTrans.ext
        funext n
        change (((_root_.SerrePositivity.ComplexLimits.rightFrameFamily A).obj.map (g.op ≫ f.op)).app n.unop).unop = _
        rw [(_root_.SerrePositivity.ComplexLimits.rightFrameFamily A).obj.map_comp]
        rfl }

/-- 概要：元の複体から単体的右 frame への自然な比較（Hovey §5.2）。
方針：同じ関手的 augmentation を leftOp で反転する。
規約：元の複体とすべての単体作用素に自然。
使われ方：始域 Hom から混合 Hom への共通図式比較。 -/
def rightSimplicialFrameAugmentation :
    Functor.const SimplexCategoryᵒᵖ ⟶ _root_.SerrePositivity.ComplexLimits.rightSimplicialFrameFamily A := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact
    { app := fun X => NatTrans.leftOp ((_root_.SerrePositivity.ComplexLimits.rightFrameFamily A).augmentation.app (op X))
      naturality := by
        intro X Y f
        apply NatTrans.ext
        funext n
        apply Quiver.Hom.op_inj
        exact (congr_app ((_root_.SerrePositivity.ComplexLimits.rightFrameFamily A).augmentation.naturality f.op) n.unop).symm }

/-- 概要：単体的右 frame の比較の各成分は擬同型（Hovey §5.2）。
方針：既存の右 frame の同じ比較の擬同型性を使う。
規約：全次元で元の複体射を保持する。
使われ方：混合 Hom の左比較の反転。 -/
lemma rightSimplicialFrameAugmentation_quasiIso (X : (Complex A))
    (n : SimplexCategoryᵒᵖ) :
    QuasiIso (((_root_.SerrePositivity.ComplexLimits.rightSimplicialFrameAugmentation A).app X).app n) :=
  _root_.SerrePositivity.ComplexLimits.rightFrameComparison_quasiIso A X n.unop

/-- 概要：右 frame のすべての値は fibrant（BM 命題 4.1）。
方針：具体的な代数モデルの全対象の fibrancy を使う。
規約：元の対象にも cofibrancy 条件はない。
使われ方：混合 Hom の左比較の終域条件。 -/
lemma rightSimplicialFrame_fibrant (X : (Complex A)) (n : SimplexCategoryᵒᵖ) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
    IsFibrant (((_root_.SerrePositivity.ComplexLimits.rightSimplicialFrameFamily A).obj X).obj n) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
  exact _root_.SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram.complex_isFibrant A _

/-- 概要：単体的右 frame の反対化は既存の Reedy cofibrant frame（Hovey §5.2）。
方針：同じ成分の既存の証明を使う。
規約：具体的なモデルを局所的に選ぶ。
使われ方：混合 Hom の右比較の入力。 -/
lemma rightSimplicialFrame_cofibrant (X : (Complex A)) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
    reedyLeft simplex (cofibrations (Complex A)ᵒᵖ)
      (initial.to ((_root_.SerrePositivity.ComplexLimits.rightSimplicialFrameFamily A).obj X).rightOp) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
  exact _root_.SerrePositivity.ComplexLimits.rightFrame_cofibrant A X

/-- 概要：単体的右 frame の反対化は homotopically constant（Hovey §5.2）。
方針：既存の右 frame の同じ単体作用素の弱同値性を使う。
規約：全次元のすべての作用素を含む。
使われ方：右 Hom 図式の Kan 性。 -/
lemma rightSimplicialFrame_homotopicallyConstant (X : (Complex A))
    {n m : SimplexCategory} (f : n ⟶ m) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    weakEquivalences (Complex A)ᵒᵖ
      (((_root_.SerrePositivity.ComplexLimits.rightSimplicialFrameFamily A).obj X).rightOp.map f) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  exact _root_.SerrePositivity.ComplexLimits.rightFrame_homotopicallyConstant A X f

end SerrePositivity.ComplexLimits
