module

public import SerrePositivity.InfinityCategories.F2.Idempotent.CompletionSlice
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits

/-!
概要：全部分圏への図式の slice は、元の slice 射影の厳密な底変換。
方針：錐の全頂点を左因子と元の図式の頂点に分け、全錐を全部分圏へ戻す。
規約：任意の添字と全次数の錐の族を扱い、頂点だけの比較にしない。
使われ方：冪等完備化による既存の極限の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全部分圏の図式への錐の族は、頂点の族が同じ部分に入れば全体も戻る。 -/
lemma fullSliceOver_lift {A K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (p : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))
    (a : A ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))
    (b : A ⟶ sliceOver (p ≫ (fullSubcomplexOnVertices X P).ι))
    (h : a ≫ (fullSubcomplexOnVertices X P).ι =
      b ≫ sliceOverProjection (p ≫ (fullSubcomplexOnVertices X P).ι)) :
    ∃ l : A ⟶ sliceOver p, l ≫ sliceOverProjection p = a ∧
      l ≫ sliceOverPostcomp p (fullSubcomplexOnVertices X P).ι = b := by
  let F := sliceOverUncurry b
  have hv : ∀ v : (join A K) _⦋0⦌, P (F.app (Opposite.op ⦋0⦌) v) := by
    rintro ⟨i, x, y⟩
    fin_cases i
    · have hy := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) y)
        (sliceOverUncurry_fixed b)
      change F.app (Opposite.op ⦋0⦌) ⟨0, x, y⟩ =
        ((p ≫ (fullSubcomplexOnVertices X P).ι).app (Opposite.op ⦋0⦌) y) at hy
      exact hy.symm ▸ fullSubcomplexOnVertices_vertex (p.app (Opposite.op ⦋0⦌) y)
    · have hx := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x)
        ((sliceOverUncurry_projection b).trans h.symm)
      change F.app (Opposite.op ⦋0⦌) ⟨1, x, y⟩ =
        ((a ≫ (fullSubcomplexOnVertices X P).ι).app (Opposite.op ⦋0⦌) x) at hx
      exact hx.symm ▸ fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) x)
  let G := fullSubcomplexLift P F hv
  have hG : G ≫ (fullSubcomplexOnVertices X P).ι = F := fullSubcomplexLift_ι _ _ _
  have hfixed : joinInr A K ≫ G = p := by
    apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
    rw [Category.assoc, hG]
    exact sliceOverUncurry_fixed b
  refine ⟨sliceOverCurry G hfixed, ?_, ?_⟩
  · apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
    rw [sliceOverCurry_projection, Category.assoc, hG]
    exact (sliceOverUncurry_projection b).trans h.symm
  · apply sliceOverUncurry_injective
    rw [sliceOverUncurry_postcomp, sliceOverUncurry_curry]
    exact hG

/-- 元の全部分圏の slice の後合成と射影の正方形は、厳密な引き戻し。 -/
lemma fullSliceOver_isPullback {K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (p : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})) :
    IsPullback (sliceOverProjection p) (sliceOverPostcomp p (fullSubcomplexOnVertices X P).ι)
      (fullSubcomplexOnVertices X P).ι
      (sliceOverProjection (p ≫ (fullSubcomplexOnVertices X P).ι)) := by
  have comm : sliceOverProjection p ≫ (fullSubcomplexOnVertices X P).ι =
      sliceOverPostcomp p (fullSubcomplexOnVertices X P).ι ≫
        sliceOverProjection (p ≫ (fullSubcomplexOnVertices X P).ι) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro c
    exact (SSet.yonedaEquiv_comp
      (joinInl (stdSimplex.obj n.unop) K ≫ c.val) (fullSubcomplexOnVertices X P).ι).symm
  apply IsPullback.mk' comm
  · intro A a b _ha hb
    apply sliceOverUncurry_injective
    apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
    exact (sliceOverUncurry_postcomp a _).symm.trans
      ((congrArg sliceOverUncurry hb).trans (sliceOverUncurry_postcomp b _))
  · intro A a b h
    obtain ⟨l, hl, hb⟩ := fullSliceOver_lift P p a b h
    exact ⟨l, hl, hb⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
