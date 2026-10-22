module

public import SerrePositivity.InfinityCategories.F2.Ind.FullJoinVertices

/-!
概要：全部分圏内の固定図式への錐の全族を、周囲の同じ錐の全族から持ち上げる。
方針：始点と固定図式の頂点条件で join 全体を持ち上げ、slice へ curry する。
規約：全パラメータと元の図式を厳密に保持する。
使われ方：Indκ 内の左 Kan 局所添字と前層内の同じ添字との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {K A X : SSet.{u}} (P : X _⦋0⦌ → Prop)
  (D : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u}))

/-- 周囲の同じ錐の全族を、同じ始点条件のもとで全部分圏内へ持ち上げる。 -/
def fullSliceLift (F : A ⟶ sliceOver (D ≫ (fullSubcomplexOnVertices X P).ι))
    (hF : ∀ a, P ((F ≫ sliceOverProjection (D ≫
      (fullSubcomplexOnVertices X P).ι)).app (Opposite.op ⦋0⦌) a)) :
    A ⟶ sliceOver D := by
  have hv : ∀ z, P ((sliceOverUncurry F).app (Opposite.op ⦋0⦌) z) := by
    apply join_vertices_property
    · rw [sliceOverUncurry_projection]
      exact hF
    · rw [sliceOverUncurry_fixed]
      intro k
      exact fullSubcomplexOnVertices_vertex (D.app (Opposite.op ⦋0⦌) k)
  let G := fullSubcomplexLift P (sliceOverUncurry F) hv
  have hG : joinInr A K ≫ G = D := by
    apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
    rw [Category.assoc, fullSubcomplexLift_ι, sliceOverUncurry_fixed]
  exact sliceOverCurry G hG

/-- 同じ持ち上げを周囲へ戻すと元の全族そのもの。 -/
lemma fullSliceLift_postcomp
    (F : A ⟶ sliceOver (D ≫ (fullSubcomplexOnVertices X P).ι))
    (hF : ∀ a, P ((F ≫ sliceOverProjection (D ≫
      (fullSubcomplexOnVertices X P).ι)).app (Opposite.op ⦋0⦌) a)) :
    fullSliceLift P D F hF ≫ sliceOverPostcomp D (fullSubcomplexOnVertices X P).ι = F := by
  apply sliceOverUncurry_injective
  rw [sliceOverUncurry_postcomp, fullSliceLift, sliceOverUncurry_curry, fullSubcomplexLift_ι]

/-- 同じ全部分包含で写した錐の全族が一致すれば、元の全族も一致する。 -/
lemma fullSlicePostcomp_cancel {f g : A ⟶ sliceOver D}
    (h : f ≫ sliceOverPostcomp D (fullSubcomplexOnVertices X P).ι =
      g ≫ sliceOverPostcomp D (fullSubcomplexOnVertices X P).ι) : f = g := by
  apply sliceOverUncurry_injective
  apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
  rw [← sliceOverUncurry_postcomp, ← sliceOverUncurry_postcomp, h]

end SerrePositivity.InfinityCategories.F2.Ind
