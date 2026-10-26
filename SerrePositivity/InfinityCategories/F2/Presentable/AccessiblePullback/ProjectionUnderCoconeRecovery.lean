module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.SourceUnderCoconeRecovery
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.StrictPullbackCocones
public import SerrePositivity.InfinityCategories.F2.Presentable.ComponentCompactOverCocones

/-!
概要：追加入力を保つ二つの全余錐から成分射影の under comma の余錐を構成する。
方針：指定始点側の余錐を回収し、両全部分包含の単射性で全値を厳密に合わせる。
規約：元の全 under 図式を保持し、同型だけの一致から貼り合わせない。
使われ方：一般 accessible 引き戻しの成分射影の cofinal 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
open HomotopyLimits

/-- 概要：compact 成分 comma の元の全 slice への包含。
方針：同じ元の頂点条件の全部分包含を使う。
規約：元の全射を保持する。
使われ方：標準入力図式と strict 余錐の対応。 -/
def componentCompactOverInclusion (μ : Cardinal.{u})
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    componentCompactOver μ p q x ⟶ sliceOver x :=
  (fullSubcomplexOnVertices (sliceOver x) (fun v ↦ ComponentCompactVertex μ p q
    ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v))).ι

/-- 概要：元の pullback 余錐と指定始点付き成分余錐の全値が整合すれば under comma に余錐がある。
方針：両 compact 全部分圏へ余錐を戻し、全値の厳密な等式で実引き戻しに貼る。
規約：元の全 under 図式と元の指定始点を保持する。
使われ方：追加入力を保つ相対交互構成から成分 cofinal 性を閉じる。 -/
lemma nonempty_projectionUnderCocone_of_extended_cocones
    {A K : SSet.{u}} {E D B C : SSet.{u + 1}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B] [Quasicategory C]
    (μ : Cardinal.{u}) (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p]
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) (π : pullback p q ⟶ C)
    (F : componentCompactOver μ p q x ⟶ compactSourceSlice μ (x ≫ π))
    (hF : F ≫ compactSourceSliceInclusion μ (x ≫ π) =
      componentCompactOverInclusion μ p q x ≫ sliceOverPostcomp x π)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ compactSourceSlice μ (x ≫ π))
    (r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ pullback (sliceUnderProjection z) F)
    (c : JoinCocone ((r ≫ pullback.snd (sliceUnderProjection z) F) ≫
      componentCompactOverInclusion μ p q x))
    (hc : ComponentCompactVertex μ p q ((sliceOverProjection x).app (Opposite.op ⦋0⦌) c.vertex))
    (hcπ : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection x ≫ π).app (Opposite.op ⦋0⦌) c.vertex))
    (d : JoinCocone (extendedSourceSliceDiagram μ (x ≫ π)
      (r ≫ pullback.fst (sliceUnderProjection z) F)))
    (hcd : c.val ≫ sliceOverPostcomp x π =
      joinMap ((SSet.uliftFunctor.{u + 1, u}).map (joinInr A K)) (𝟙 Δ[0]) ≫ d.val) :
    Nonempty (JoinCocone r) := by
  let P := sliceUnderProjection z
  let t := r ≫ pullback.fst P F
  let a := r ≫ pullback.snd P F
  let Q := fun v : (sliceOver x) _⦋0⦌ ↦
    ComponentCompactVertex μ p q ((sliceOverProjection x).app (Opposite.op ⦋0⦌) v)
  let cy := fullSubcomplexCoconeLift Q a c hc
  have hv := cocone_vertex_image_eq_of_val_eq_restrict (sliceOverPostcomp x π)
    ((SSet.uliftFunctor.{u + 1, u}).map (joinInr A K)) c d hcd
  have hd : Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection (x ≫ π)).app (Opposite.op ⦋0⦌) d.vertex) := by
    rw [← hv]
    have hπ := congrArg (fun g ↦ g.app (Opposite.op ⦋0⦌) c.vertex)
      (F1B.sliceOverPostcomp_projection x π)
    exact hπ.symm ▸ hcπ
  obtain ⟨ct, hct⟩ := exists_sourceUnderCocone_of_extendedInputCocone μ (x ≫ π) t d hd
  have hcy : cy.val ≫ componentCompactOverInclusion μ p q x = c.val := by
    exact fullSubcomplexLift_ι Q c.val (fullSubcomplexCocone_vertices Q a c hc)
  have hstrict : ct.val ≫ P = cy.val ≫ F := by
    apply (cancel_mono (compactSourceSliceInclusion μ (x ≫ π))).1
    calc
      _ = joinMap ((SSet.uliftFunctor.{u + 1, u}).map (joinInr A K)) (𝟙 Δ[0]) ≫ d.val := hct
      _ = c.val ≫ sliceOverPostcomp x π := hcd.symm
      _ = (cy.val ≫ componentCompactOverInclusion μ p q x) ≫ sliceOverPostcomp x π := by
        rw [hcy]
      _ = _ := by simp only [Category.assoc]; rw [hF]
  exact ⟨strictPullbackCocone P F r ct cy hstrict⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
