module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionFirstBottomMerge
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRefinementFaces

/-!
概要：元の非退化な原子から最初の併合を選び、一つ高次の原子的な実全単体を構成する。
方針：証明済みの有限最小元と実併合・実残余射を元の実全鎖へ挿入する。
規約：位置・辺の併合条件・原子性・指定面の等式を仮定しない。
使われ方：Riehl–Verity §4.1–§4.2の原子の親の実候補、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の全coherentな随伴の入力。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：元の正の次元の非退化な原子の最初の併合で細分した実全単体。
方針：原子性から終頂点の一点を取り、実最小元とその所属から全ての射を構成する。
規約：位置や併合の証人を入力に追加しない。使われ方：Riehl–Verity §4.1の実親の候補。 -/
def walkingAdjunctionFirstRefinement {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2) :=
  let hlast := (walkingAdjunctionAtomic_endpoint_cards H ha).2
  let k := walkingAdjunctionFirstBottomMergeIndex H hlast hnd
  let hk := walkingAdjunctionFirstBottomMergeIndex_spec H hlast hnd
  walkingAdjunctionBottomMergeRefinement H k
    (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) - 2)
    (Nat.sub_add_cancel hk.card_two_le).symm hk.one_zero

/-- 概要：最初の併合で細分した実全単体は原子的。
方針：構成済みの実細分の原子性の保存を適用する。
規約：全実分解を含む原子性を結論とする。使われ方：Riehl–Verity §4.1の原子の実細分。 -/
lemma walkingAdjunctionFirstRefinement_atomic {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩)
      (walkingAdjunctionFirstRefinement H ha hnd) :=
  walkingAdjunctionBottomMergeRefinement_atomic H _ _ _ _ ha

/-- 概要：選んだ最初の実細分の指定面は元の実全単体。
方針：実最小元で構成した辺へ全関手の指定面の回収を適用する。
規約：指定面の等式を結論として得る。使われ方：Riehl–Verity §4.1の実親の指定面。 -/
lemma walkingAdjunctionFirstRefinement_face {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    finiteChainFace (walkingAdjunctionFirstRefinement H ha hnd)
      (walkingAdjunctionFirstBottomMergeIndex H
        (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd).succ.castSucc = H :=
  walkingAdjunctionBottomMergeRefinement_face H _ _ _ _

/-- 概要：選んだ最初の実細分に元のnerveの指定面を作用させると元へ戻る。
方針：実位置と実全鎖からの面の等式を元の単体集合へ移す。
規約：元のHomの実単体作用の等式。使われ方：Riehl–Verity §4.1の実親の面の検収。 -/
lemma walkingAdjunctionFirstRefinement_nerve_face {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : Fin (n + 2) ⥤ walkingAdjunctionHom .minus Y)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.minus⟩) (Y := ⟨Y⟩) H)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    (((WalkingAdjunctionHomShape.{u} .minus Y).map (SimplexCategory.δ
      (walkingAdjunctionFirstBottomMergeIndex H
        (walkingAdjunctionAtomic_endpoint_cards H ha).2 hnd).succ.castSucc).op)
          (ULift.up (walkingAdjunctionFirstRefinement H ha hnd))).down = H := by
  rw [walkingAdjunctionHomShape_face]
  exact walkingAdjunctionFirstRefinement_face H ha hnd

end SerrePositivity.InfinityCategories.HA.Monads
