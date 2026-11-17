module

public import SerrePositivity.EInfinity.BarrattEccles.WeightedCotensorCarrier
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation

/-!
# 元の右 frame を底の複体で使うための条件

概要：BM 命題 4.1・Hovey §5.2 の同じ E 代数右 frame を複体へ忘却する。
方針：反対忘却の左 Quillen 性と実際の latching 比較の保存を使う。
規約：frame・augmentation・元の図式を選び直さない。
使われ方：一般 homotopy 極限の底の右導来極限比較。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory Limits _root_.HomotopicalAlgebra Opposite
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：反対忘却は具体的な両モデルで左 Quillen（BM 命題 4.1）。
方針：忘却の二つの右類の保存を反対化する。
規約：モデル構造は局所的に選び、追加の入力にはしない。
使われ方：同じ右 frame の底での Reedy cofibrancy。 -/
lemma forgetOp_isLeftQuillen :
    let := projectiveModelCategory A
    let := modelCategory A
    SerrePositivity.Quillen.IsLeftQuillen (Operad.Algebra.forget (operad A)).op := by
  let := projectiveModelCategory A
  let := modelCategory A
  have h := forget_isRightQuillen A
  exact ⟨fun _ _ f hf => h.map_fibrations f.unop hf,
    fun _ _ f hf => h.map_trivialFibrations f.unop hf⟩

/-- 概要：実際の右 frame の底の余単体図式（Hovey §5.2）。
方針：元の右 frame を反対忘却で後合成する。
規約：各次数・作用素は元の同じ射。
使われ方：底の重み付き end とその Hom の係数。 -/
def carrierRightFrame (X : (operad A).Algebra) : SimplexCategory ⥤ (Complex A)ᵒᵖ :=
  rightFrame A X ⋙ (Operad.Algebra.forget (operad A)).op

/-- 概要：底の右 frame は反対圏で Reedy cofibrant（Hovey §5.2）。
方針：反対忘却の左随伴性と左 Quillen 性で元の latching 比較を移す。
規約：底の元の複体の cofibrancy は不要。
使われ方：底の frame Hom の Kan 性と重み付き実現の π₀ 比較。 -/
lemma carrierRightFrame_cofibrant (X : (operad A).Algebra) :
    let := projectiveModelCategory A
    reedyLeft simplex (cofibrations (Complex A)ᵒᵖ) (initial.to (carrierRightFrame A X)) := by
  let := projectiveModelCategory A
  let := modelCategory A
  let U := Operad.Algebra.forget (operad A)
  have : U.op.IsLeftAdjoint := (operad A).freeAlgebraAdjunction.op.isLeftAdjoint
  have := forgetOp_isLeftQuillen A
  exact leftQuillen_frame_reedyCofibrant U.op (rightFrame A X) (rightFrame_cofibrant A X)

/-- 概要：底の右 frame はホモトピー定値（Hovey §5.2）。
方針：元の全単体作用素の弱同値性を擬同型として忘却する。
規約：全次元・すべての単体作用素。
使われ方：底の重み付き錐の π₀ の局所化 Hom 比較。 -/
lemma carrierRightFrame_homotopicallyConstant (X : (operad A).Algebra)
    {n m : SimplexCategory} (f : n ⟶ m) :
    let := projectiveModelCategory A
    weakEquivalences (Complex A)ᵒᵖ ((carrierRightFrame A X).map f) := by
  let := projectiveModelCategory A
  let := modelCategory A
  exact rightFrame_homotopicallyConstant A X f

/-- 概要：底の右 frame から元の定値複体への augmentation（Hovey §5.2）。
方針：元の右 frame の augmentation を同じ忘却で移す。
規約：元の比較射の反対射そのもの。
使われ方：底の通常錐の重み付き族。 -/
def carrierRightFrameAugmentation (X : (operad A).Algebra) :
    carrierRightFrame A X ⟶ (Functor.const SimplexCategory).obj (op X.carrier) := by
  let := modelCategory A
  exact Functor.whiskerRight ((rightFrameFamily A).augmentation.app (op X))
    (Operad.Algebra.forget (operad A)).op

/-- 概要：底の augmentation は各次数で擬同型（Hovey §5.2）。
方針：同じ元の右 frame 比較の擬同型性を使う。
規約：置換を選び直さず元の比較を保持する。
使われ方：底の錐の元の図式との照合。 -/
lemma carrierRightFrameAugmentation_quasiIso (X : (operad A).Algebra)
    (n : SimplexCategory) :
    QuasiIso ((carrierRightFrameAugmentation A X).app n).unop := by
  exact rightFrameComparison_quasiIso A X n

/-- 概要：図式の底の frame の各値は同じ右 frame（Hovey §5.2）。
方針：後合成の対象の定義を展開する。
規約：元の添字の反対を保持する。
使われ方：底の重み付き end へ frame の条件を代入する。 -/
lemma carrierRightFrameDiagram_obj (K : Type u) [SmallCategory K]
    (F : K ⥤ (operad A).Algebra) (k : Kᵒᵖ) :
    (carrierRightFrameDiagram A K F).obj k = carrierRightFrame A (F.obj k.unop) := rfl

end SerrePositivity.EInfinity.BarrattEccles
