module

public import SerrePositivity.InfinityCategories.F2.Ind.FullJoinVertices
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalCosliceSource

/-!
概要：全部分圏内の図式上の余錐の全族を、周囲の同じ余錐の全族から持ち上げる。
方針：図式側の頂点と余錐頂点の条件で join 全体を全部分複体へ持ち上げて curry する。
規約：周囲の全図式とパラメータを厳密に保持する。
使われ方：Ind の包含による余極限の反映と余錐の構成。
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

/-- 周囲の余錐の全族を、同じ頂点条件のもとで全部分圏内の全族へ持ち上げる。 -/
def fullCosliceLift (F : A ⟶ sliceUnder (D ≫ (fullSubcomplexOnVertices X P).ι))
    (hF : ∀ a, P ((F ≫ sliceUnderProjection (D ≫
      (fullSubcomplexOnVertices X P).ι)).app (Opposite.op ⦋0⦌) a)) :
    A ⟶ sliceUnder D := by
  have hv : ∀ z, P ((sliceUnderUncurry F).app (Opposite.op ⦋0⦌) z) := by
    apply join_vertices_property
    · rw [sliceUnderUncurry_fixed]
      intro k
      exact fullSubcomplexOnVertices_vertex (D.app (Opposite.op ⦋0⦌) k)
    · rw [sliceUnderUncurry_projection]
      exact hF
  let G := fullSubcomplexLift P (sliceUnderUncurry F) hv
  have hG : joinInl K A ≫ G = D := by
    apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
    rw [Category.assoc, fullSubcomplexLift_ι, sliceUnderUncurry_fixed]
  exact sliceUnderCurry G hG

/-- 同じ持ち上げを周囲へ戻すと元の余錐の全族そのもの。 -/
lemma fullCosliceLift_postcomp
    (F : A ⟶ sliceUnder (D ≫ (fullSubcomplexOnVertices X P).ι))
    (hF : ∀ a, P ((F ≫ sliceUnderProjection (D ≫
      (fullSubcomplexOnVertices X P).ι)).app (Opposite.op ⦋0⦌) a)) :
    fullCosliceLift P D F hF ≫ sliceUnderPostcomp D (fullSubcomplexOnVertices X P).ι = F := by
  apply sliceUnderUncurry_injective
  rw [sliceUnderUncurry_postcomp, fullCosliceLift, sliceUnderUncurry_curry,
    fullSubcomplexLift_ι]

/-- 同じ全部分包含で写した余錐の全族が一致すれば、元の全族も一致する。 -/
lemma fullCoslicePostcomp_cancel {f g : A ⟶ sliceUnder D}
    (h : f ≫ sliceUnderPostcomp D (fullSubcomplexOnVertices X P).ι =
      g ≫ sliceUnderPostcomp D (fullSubcomplexOnVertices X P).ι) : f = g := by
  apply sliceUnderUncurry_injective
  apply (cancel_mono (fullSubcomplexOnVertices X P).ι).mp
  rw [← sliceUnderUncurry_postcomp, ← sliceUnderUncurry_postcomp, h]

end SerrePositivity.InfinityCategories.F2.Ind
