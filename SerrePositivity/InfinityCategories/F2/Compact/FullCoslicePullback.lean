module

public import SerrePositivity.InfinityCategories.F1.Compact.ClassificationTransport
public import SerrePositivity.InfinityCategories.Core.TerminalVertices
public import SerrePositivity.InfinityCategories.Core.JoinLifting
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits

/-!
概要：全部分圏の元の coslice 射影は、元の包含に沿う厳密な底変換。
方針：元の全余錐族の頂点条件から同じ全図式を部分圏へ回収する。
規約：元の始点・元の全写像・元の射影を同時に保持。
使われ方：全部分包含による元の全共変 Hom の自然比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の全部分圏の図式への錐の族は、頂点の族が同じ部分に入れば全体も戻る。 -/
lemma fullSliceUnder_lift {A K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (p : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))
    (a : A ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))
    (b : A ⟶ sliceUnder (p ≫ (fullSubcomplexOnVertices X P).ι))
    (h : a ≫ (fullSubcomplexOnVertices X P).ι =
      b ≫ sliceUnderProjection (p ≫ (fullSubcomplexOnVertices X P).ι)) :
    ∃ l : A ⟶ sliceUnder p, l ≫ sliceUnderProjection p = a ∧
      l ≫ sliceUnderPostcomp p (fullSubcomplexOnVertices X P).ι = b := by
  let F := sliceUnderUncurry b
  have hv : ∀ v : (join K A) _⦋0⦌, P (F.app (Opposite.op ⦋0⦌) v) := by
    rintro ⟨i, x, y⟩
    fin_cases i
    · have hy := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) y)
        ((sliceUnderUncurry_projection b).trans h.symm)
      change F.app (Opposite.op ⦋0⦌) ⟨0, x, y⟩ =
        ((a ≫ (fullSubcomplexOnVertices X P).ι).app (Opposite.op ⦋0⦌) y) at hy
      exact hy.symm ▸ fullSubcomplexOnVertices_vertex (a.app (Opposite.op ⦋0⦌) y)
    · have hx := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x)
        (sliceUnderUncurry_fixed b)
      change F.app (Opposite.op ⦋0⦌) ⟨1, x, y⟩ =
        ((p ≫ (fullSubcomplexOnVertices X P).ι).app (Opposite.op ⦋0⦌) x) at hx
      exact hx.symm ▸ fullSubcomplexOnVertices_vertex (p.app (Opposite.op ⦋0⦌) x)
  let G := fullSubcomplexLift P F hv
  have hG : G ≫ (fullSubcomplexOnVertices X P).ι = F := fullSubcomplexLift_ι _ _ _
  have hfixed : joinInl K A ≫ G = p := by
    apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
    rw [Category.assoc, hG]
    exact sliceUnderUncurry_fixed b
  refine ⟨sliceUnderCurry G hfixed, ?_, ?_⟩
  · apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
    rw [sliceUnderCurry_projection, Category.assoc, hG]
    exact (sliceUnderUncurry_projection b).trans h.symm
  · apply sliceUnderUncurry_injective
    rw [sliceUnderUncurry_postcomp, sliceUnderUncurry_curry]
    exact hG

/-- 元の全部分圏の slice の後合成と射影の正方形は、厳密な引き戻し。 -/
lemma fullSliceUnder_isPullback {K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (p : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})) :
    IsPullback (sliceUnderProjection p) (sliceUnderPostcomp p (fullSubcomplexOnVertices X P).ι)
      (fullSubcomplexOnVertices X P).ι
      (sliceUnderProjection (p ≫ (fullSubcomplexOnVertices X P).ι)) := by
  have comm : sliceUnderProjection p ≫ (fullSubcomplexOnVertices X P).ι =
      sliceUnderPostcomp p (fullSubcomplexOnVertices X P).ι ≫
        sliceUnderProjection (p ≫ (fullSubcomplexOnVertices X P).ι) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro c
    exact (SSet.yonedaEquiv_comp
      (joinInr K (stdSimplex.obj n.unop) ≫ c.val) (fullSubcomplexOnVertices X P).ι).symm
  apply IsPullback.mk' comm
  · intro A a b _ha hb
    apply sliceUnderUncurry_injective
    apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
    exact (sliceUnderUncurry_postcomp a _).symm.trans
      ((congrArg sliceUnderUncurry hb).trans (sliceUnderUncurry_postcomp b _))
  · intro A a b h
    obtain ⟨l, hl, hb⟩ := fullSliceUnder_lift P p a b h
    exact ⟨l, hl, hb⟩

end SerrePositivity.InfinityCategories.F2.Compact
