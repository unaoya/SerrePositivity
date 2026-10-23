module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.ConeFamilyPullbackLimit
public import SerrePositivity.InfinityCategories.Core.PullbackSimplex

/-!
概要：像の全錐が一致する二成分の錐を引き戻し内の錐へ貼る。
方針：図式固定の錐族の引き戻し同型を零単体に適用する。
規約：元の図式と選んだ両成分の全錐を厳密に保持する。
使われ方：lax pullback の極限錐の存在と指定両成分の回収。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：適合した二成分の錐を元の引き戻し図式の錐へ厳密に合わせる。
方針：錐族の引き戻しの頂点を作り、その逆同型と錐の全単射を使う。
規約：この貼り合わせには quasicategory 性も極限性も要求しない。
使われ方：両入力を保持した極限錐の存在構成。 -/
lemma exists_cone_pullback_with_components {J E D B : SSet.{u}}
    (p : E ⟶ B) (q : D ⟶ B) (r : J ⟶ pullback p q)
    (ce : JoinCone (r ≫ pullback.fst p q)) (cd : JoinCone (r ≫ pullback.snd p q))
    (h : ce.val ≫ p = cd.val ≫ q) :
    ∃ c : JoinCone r, mapJoinCone (pullback.fst p q) c = ce ∧
      mapJoinCone (pullback.snd p q) c = cd := by
  let xe := coneFamilyVertexEquiv (r ≫ pullback.fst p q) ce
  let xd := coneFamilyVertexEquiv (r ≫ pullback.snd p q) cd
  have hm : (coneFamilyPostcomp (r ≫ pullback.fst p q) p).app (Opposite.op ⦋0⦌) xe =
      (coneFamilyPullbackBaseMap p q r).app (Opposite.op ⦋0⦌) xd := by
    apply Subtype.ext
    have hd := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) xd)
      (coneFamilyPullbackBaseMap_ι p q r)
    change ((coneFamilyPullbackBaseMap p q r).app (Opposite.op ⦋0⦌) xd).val =
      functorVertex (cd.val ≫ q) at hd
    change ((coneFamilyPostcomp (r ≫ pullback.fst p q) p).app
      (Opposite.op ⦋0⦌) xe).val = _
    dsimp only [xe]
    rw [coneFamilyPostcomp_vertex]
    change functorVertex (ce.val ≫ p) = _
    exact (congrArg functorVertex h).trans hd.symm
  let sq := coneFamilyPullback_isPullback p q r
  let v := pullbackSimplex (coneFamilyPostcomp (r ≫ pullback.fst p q) p)
    (coneFamilyPullbackBaseMap p q r) xe xd hm
  let z := sq.isoPullback.inv.app (Opposite.op ⦋0⦌) v
  let c := (coneFamilyVertexEquiv r).symm z
  have hcz : coneFamilyVertexEquiv r c = z := (coneFamilyVertexEquiv r).apply_symm_apply z
  refine ⟨c, ?_, ?_⟩
  · apply (coneFamilyVertexEquiv (r ≫ pullback.fst p q)).injective
    rw [← coneFamilyPostcomp_vertex, hcz]
    have he := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v) sq.isoPullback_inv_fst
    exact he.trans (pullbackSimplex_fst _ _ _ _ _)
  · apply (coneFamilyVertexEquiv (r ≫ pullback.snd p q)).injective
    rw [← coneFamilyPostcomp_vertex, hcz]
    have hd := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) v) sq.isoPullback_inv_snd
    exact hd.trans (pullbackSimplex_snd _ _ _ _ _)

end SerrePositivity.InfinityCategories.F2
