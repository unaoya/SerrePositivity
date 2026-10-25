module

public import SerrePositivity.InfinityCategories.F2.Presentable.SliceOverCoconeFromColimit
public import SerrePositivity.InfinityCategories.HomotopyLimits.FullSubcomplexCoconeLift
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.CoconeTransformationPointPost

/-!
概要：頂点条件で切り出した対象上の図式へ、条件を保つ余錐を構成する。
方針：底の余極限の条件を対象上の余錐頂点へ移し、全部分複体へ戻す。
規約：元の全図式と指定余極限余錐を保持する。
使われ方：compact 成分を持つ comma の filtered 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：頂点条件が指定余極限頂点で成立すれば、対象上の内部余錐がある。
方針：対象上の余錐を作り、射影の全等式で頂点条件を移す。
規約：頂点条件には同型不変性を仮定しない。
使われ方：compact 成分の図式を同じ対象上で上から抑える。 -/
lemma exists_predicateOver_cocone_lifting_colimit {K X : SSet.{u}}
    (P : X _⦋0⦌ → Prop) (x : (Δ[0] : SSet.{u}) ⟶ X)
    (r : K ⟶ (fullSubcomplexOnVertices (sliceOver x)
      (fun v ↦ P ((sliceOverProjection x).app _ v)) : SSet.{u}))
    (c : JoinCocone ((r ≫ (fullSubcomplexOnVertices (sliceOver x)
      (fun v ↦ P ((sliceOverProjection x).app _ v))).ι) ≫ sliceOverProjection x))
    (hc : IsColimitCone c) (hP : P c.vertex) :
    ∃ d : JoinCocone r, (d.val ≫ (fullSubcomplexOnVertices (sliceOver x)
      (fun v ↦ P ((sliceOverProjection x).app _ v))).ι) ≫ sliceOverProjection x = c.val := by
  let Q := fun v ↦ P ((sliceOverProjection x).app _ v)
  let j := (fullSubcomplexOnVertices (sliceOver x) Q).ι
  obtain ⟨d, hd⟩ := exists_sliceOver_cocone_lifting_colimit x (r ≫ j) c hc
  have hv : (sliceOverProjection x).app _ d.vertex = c.vertex := by
    rw [← Ind.mapJoinCocone_vertex]
    exact congrArg JoinCocone.vertex (show mapJoinCocone (sliceOverProjection x) d = c from
      Subtype.ext hd)
  have hQ : Q d.vertex := by
    dsimp only [Q]
    rw [hv]
    exact hP
  let d' := HomotopyLimits.fullSubcomplexCoconeLift Q r d hQ
  refine ⟨d', ?_⟩
  have he := congrArg Subtype.val
    (HomotopyLimits.fullSubcomplexCoconeLift_inclusion Q r d hQ)
  change (d'.val ≫ j) ≫ sliceOverProjection x = c.val
  change d'.val ≫ j = d.val at he
  rw [he, hd]

end SerrePositivity.InfinityCategories.F2.Presentable
