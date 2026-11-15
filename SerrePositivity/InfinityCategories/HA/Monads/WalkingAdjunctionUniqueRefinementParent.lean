module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomMergeRigidity
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionRefinementNondegenerateIff

/-!
概要：非退化な指定面を持つ純粋な併合の実親の存在・一意性を非純粋性と照合する。
方針：構成済みの実細分の非退化性の両方向と全実関手の一意性を合わせる。
規約：原典の文字列表示との全比較とは区別し、元の四Homのnerveの条件を示す。
使われ方：Riehl–Verity §4.1–§4.2の親の対応、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実細分の照合。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：指定位置の純粋な併合を持つ非退化な実親は、元の辺が非純粋のとき一意に存在。
方針：実細分で存在を作り、指定面と左辺の全点条件から全関手の一意性を得る。
規約：元のnerveでの非退化性を結論に含む。使われ方：Riehl–Verity §4.1の実親の対応。 -/
lemma walkingAdjunctionBottomMergeRefinement_existsUnique_nondegenerate_iff
    {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 1)) (k : Fin (n + 1))
    (m : ℕ) (hA : walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc) = m + 2)
    (h1 : ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      i.val = 1 → (walkingAdjunctionOrderHom (H.map
        (homOfLE (Fin.castSucc_le_succ k))) i).val = 0)
    (hnd : ULift.up H ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 1)) :
    (∃! P : ComposableArrows (walkingAdjunctionHom .minus Y) (n + 2),
      ULift.up P ∈ (WalkingAdjunctionHomShape.{u} .minus Y).nonDegenerate (n + 2) ∧
      finiteChainFace P k.succ.castSucc = H ∧
      walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (P.obj k.castSucc.castSucc)),
        (walkingAdjunctionOrderHom (P.map
          (homOfLE (Fin.castSucc_le_succ k.castSucc))) i).val = i.val - 1) ↔
    ¬ (walkingAdjunctionOrdinalCard .minus Y (H.obj k.succ) = m + 1 ∧
      ∀ i : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
        (walkingAdjunctionOrderHom (H.map (homOfLE (Fin.castSucc_le_succ k))) i).val =
          i.val - 1) := by
  let G := walkingAdjunctionBottomMergeRefinement H k m hA h1
  have hiff := walkingAdjunctionBottomMergeRefinement_nondegenerate_iff_not_pure H k m hA h1 hnd
  constructor
  · rintro ⟨P, hP, _⟩
    have he := walkingAdjunctionBottomMergeRefinement_unique H k m hA h1 P hP.2.1 hP.2.2
    exact hiff.mp (he ▸ hP.1)
  · intro hp
    refine ⟨G, ⟨hiff.mpr hp,
      walkingAdjunctionBottomMergeRefinement_face H k m hA h1,
      walkingAdjunctionBottomMergeRefinement_pure H k m hA h1⟩, ?_⟩
    intro P hP
    exact walkingAdjunctionBottomMergeRefinement_unique H k m hA h1 P hP.2.1 hP.2.2

end SerrePositivity.InfinityCategories.HA.Monads
