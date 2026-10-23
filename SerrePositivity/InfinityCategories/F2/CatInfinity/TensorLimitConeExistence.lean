module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.TensorConeComponentCriterion

/-!
概要：選んだ両成分の極限錐を厳密に保つ直積の極限錐の存在。
方針：錐族の直積同型の逆で二つの錐を合わせ、元の錐へ戻す。
規約：頂点だけでなく両成分の全錐を保持する。
使われ方：lax pullback の選択された入力の極限錐。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定した両成分の極限錐を保つ直積内の極限錐が存在する。
方針：錐族同型の逆と頂点の全単射を使い、二射影の等式を回収する。
規約：元の図式 r と選んだ二つの錐を厳密に保持する。
使われ方：両入力を固定した lax pullback の極限錐の構成。 -/
lemma exists_limitCone_tensor_with_components {J X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (r : J ⟶ X ⊗ Y)
    (cx : JoinCone (r ≫ fst X Y)) (cy : JoinCone (r ≫ snd X Y))
    (hx : IsLimitCone cx) (hy : IsLimitCone cy) :
    ∃ c : JoinCone r, IsLimitCone c ∧ mapJoinCone (fst X Y) c = cx ∧
      mapJoinCone (snd X Y) c = cy := by
  let v := (coneFamilyVertexEquiv (r ≫ fst X Y) cx,
    coneFamilyVertexEquiv (r ≫ snd X Y) cy)
  let z := (coneFamilyTensorIso r).inv.app (Opposite.op ⦋0⦌) v
  let c := (coneFamilyVertexEquiv r).symm z
  have hcz : coneFamilyVertexEquiv r c = z := (coneFamilyVertexEquiv r).apply_symm_apply z
  have hz := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v) (coneFamilyTensorIso r).inv_hom_id
  change (coneFamilyTensorIso r).hom.app (Opposite.op ⦋0⦌) z = v at hz
  rw [← hcz, coneFamilyTensorIso_vertex] at hz
  have hcx : mapJoinCone (fst X Y) c = cx :=
    (coneFamilyVertexEquiv (r ≫ fst X Y)).injective (congrArg Prod.fst hz)
  have hcy : mapJoinCone (snd X Y) c = cy :=
    (coneFamilyVertexEquiv (r ≫ snd X Y)).injective (congrArg Prod.snd hz)
  refine ⟨c, isLimitCone_tensor_of_components c ?_ ?_, hcx, hcy⟩
  · rwa [hcx]
  · rwa [hcy]

end SerrePositivity.InfinityCategories.F2
