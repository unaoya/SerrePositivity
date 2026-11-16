module

public import SerrePositivity.InfinityCategories.HA.Monads.ComposableArrowRefinementFaces
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionAtomicRefinement
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionDegeneracies

/-!
概要：実併合で細分した全単体の指定面を、元のnerveの実面として検収する。
方針：一点を飛ばす実順序関手を単体圏の面に照合し、実因子化の等式を適用する。
規約：別の面の模型だけで終えず、元のHomの単体集合の作用との等式を保持する。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の指定面、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前のcoherentな随伴の実面。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：実鎖の面の添字関手は単体圏の実面の順序関手。
方針：同じsuccAboveの実定義を使う。規約：全射の作用を含む。
使われ方：Riehl–Verity §4.1の元の面との照合。 -/
lemma finiteChainFaceIndex_simplex {n : ℕ} (k : Fin (n + 2)) :
    finiteChainFaceIndex k = walkingAdjunctionSimplexFunctor (SimplexCategory.δ k) := by
  rfl

/-- 概要：元の全Homのnerveの実面は構成した実鎖の面。
方針：nerveと宇宙持ち上げの実定義を照合する。規約：元の単体集合の作用。
使われ方：Riehl–Verity §4.1の指定面の検収。 -/
lemma walkingAdjunctionHomShape_face {n : ℕ} (X Y : WalkingAdjunctionPoint)
    (k : Fin (n + 2)) (F : ComposableArrows (walkingAdjunctionHom X Y) (n + 1)) :
    (((WalkingAdjunctionHomShape.{u} X Y).map (SimplexCategory.δ k).op) (ULift.up F)).down =
      finiteChainFace F k := by
  rfl

/-- 概要：実併合で細分した実全単体の指定面は元の実全単体。
方針：元の実射の因子化の等式を、実鎖の指定面の合成則に適用する。
規約：元のHomへの全関手の等式。使われ方：Riehl–Verity §4.1の親の指定面。 -/
lemma walkingAdjunctionBottomMergeRefinement_face {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    finiteChainFace (walkingAdjunctionBottomMergeRefinement H k m hA h1) k.succ.castSucc = H :=
  composableArrowRefinement_face n H k _ _ _
    (walkingAdjunctionBottomMerge_factor (H.map (homOfLE (Fin.castSucc_le_succ k))) m hA h1)

/-- 概要：実併合で細分した全単体に元のnerveの指定面を作用させると元へ戻る。
方針：元の全Homの面の照合と実鎖の面の等式を合わせる。
規約：元の単体集合の実作用の等式。使われ方：Riehl–Verity §4.1の実親の面の検収。 -/
lemma walkingAdjunctionBottomMergeRefinement_nerve_face {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0) :
    (((WalkingAdjunctionHomShape.{u} .minus Y).map
      (SimplexCategory.δ k.succ.castSucc).op)
        (ULift.up (walkingAdjunctionBottomMergeRefinement H k m hA h1))).down = H := by
  rw [walkingAdjunctionHomShape_face]
  exact walkingAdjunctionBottomMergeRefinement_face H k m hA h1

end SerrePositivity.InfinityCategories.HA.Monads
