module

public import SerrePositivity.InfinityCategories.F2.Ind.FullCosliceLift
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationCocone

/-!
概要：全部分包含は、元の同じ余錐の native な余極限性を反映する。
方針：周囲の coslice 内の始対象の境界充填を、全頂点の条件で元の全部分 coslice へ戻す。
規約：充満忠実性や余極限性を追加の instance 仮定にしない。
使われ方：Ind の前層内の余極限から、同じ Ind 内の余極限を得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 全部分包含で写した同じ余錐が余極限なら、元の余錐も余極限。 -/
lemma isColimitCone_of_fullInclusion {K X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    {D : K ⟶ (fullSubcomplexOnVertices X P : SSet.{u})} (c : JoinCocone D)
    (hc : IsColimitCone (mapJoinCocone (fullSubcomplexOnVertices X P).ι c)) :
    IsColimitCone c := by
  let q := sliceUnderPostcomp D (fullSubcomplexOnVertices X P).ι
  have hi : IsInitialVertex (q.app (Opposite.op ⦋0⦌) c) := hc
  intro n b hb
  have hqb : boundaryVertex n 0 ≫ (b ≫ q) =
      SSet.yonedaEquiv.symm (q.app (Opposite.op ⦋0⦌) c) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
  obtain ⟨F, hF⟩ := hi n (b ≫ q) hqb
  have hv : ∀ v, P ((F ≫ sliceUnderProjection
      (D ≫ (fullSubcomplexOnVertices X P).ι)).app (Opposite.op ⦋0⦌) v) := by
    intro v
    have hvb : v ∈ (boundary (n + 1)).obj (Opposite.op ⦋0⦌) := by
      have hz : stdSimplex.obj₀Equiv.symm (stdSimplex.obj₀Equiv v) = v :=
        Equiv.symm_apply_apply _ v
      have h := vertex_mem_boundary n (stdSimplex.obj₀Equiv v)
      rw [hz] at h
      exact h
    let w : (boundary (n + 1) : SSet.{u}) _⦋0⦌ := ⟨v, hvb⟩
    have he : F.app (Opposite.op ⦋0⦌) v = (b ≫ q).app (Opposite.op ⦋0⦌) w :=
      ConcreteCategory.congr_hom (NatTrans.congr_app hF (Opposite.op ⦋0⦌)) w
    change P ((sliceUnderProjection _).app (Opposite.op ⦋0⦌)
      (F.app (Opposite.op ⦋0⦌) v))
    rw [he]
    change P (((sliceUnderPostcomp D (fullSubcomplexOnVertices X P).ι ≫
      sliceUnderProjection (D ≫ (fullSubcomplexOnVertices X P).ι)).app (Opposite.op ⦋0⦌))
        (b.app (Opposite.op ⦋0⦌) w))
    rw [sliceUnderPostcomp_projection]
    exact fullSubcomplexOnVertices_vertex
      ((sliceUnderProjection D).app (Opposite.op ⦋0⦌) (b.app (Opposite.op ⦋0⦌) w))
  let L := fullCosliceLift P D F hv
  refine ⟨L, ?_⟩
  apply fullCoslicePostcomp_cancel P D
  change (boundary (n + 1)).ι ≫ (L ≫ q) = b ≫ q
  rw [show L ≫ q = F from fullCosliceLift_postcomp P D F hv, hF]

end SerrePositivity.InfinityCategories.F2.Ind
