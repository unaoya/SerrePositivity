module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedArrows
public import SerrePositivity.InfinityCategories.F2.Presentable.CompactEquivalence
public import SerrePositivity.InfinityCategories.F2.Ind.NativeCoconePreservationTransport

/-!
概要：飽和射圏の包含は、元の任意の小余極限を保存する。
方針：周囲の余錐の持ち上げで得た普遍余錐から、元の指定余錐へ保存性を移す。
規約：一つの選択余錐だけでなく全ての指定余錐を量化する。
使われ方：P-1 f2、周囲の compact 性を飽和射圏に反映する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 飽和射圏の元の全小余極限は、周囲の射圏の同じ全余極限である。 -/
lemma generatedArrowInclusion_preservesSmallColimits
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌) :
    PreservesSmallColimits (generatedArrowInclusion edges) := by
  intro K D c hc
  obtain ⟨c₀, hc₀⟩ := functor_hasSmallColimits (Δ[1] : SSet.{u + 1}) hC K
    (D ≫ generatedArrowInclusion edges)
  let P := fun f ↦ arrowVertexEdge f ∈ generatedEdges edges
  let d := Ind.fullCoconeLift P D c₀ (generatedArrow_colimit_mem edges D c₀ hc₀)
  have hd : IsColimitCone d := Ind.fullCoconeLift_isColimit P D c₀
    (generatedArrow_colimit_mem edges D c₀ hc₀) hc₀
  have hi : IsColimitCone (mapJoinCocone (generatedArrowInclusion edges) d) := by
    change IsColimitCone (mapJoinCocone (fullSubcomplexOnVertices _ P).ι
      (Ind.fullCoconeLift P D c₀ (generatedArrow_colimit_mem edges D c₀ hc₀)))
    rw [Ind.fullCoconeLift_inclusion]
    exact hc₀
  exact Ind.mapJoinCocone_isColimit_of_functorIso (generatedArrowInclusion edges)
    (Iso.refl _) d c hd hc hi

/-- 周囲の射圏で compact な元の飽和射は、飽和射圏の中でも compact。 -/
lemma generatedArrow_isKappaCompact_of_image {κ : Cardinal.{u}}
    (hC : HasSmallColimits C) (edges : I → C _⦋1⦌)
    (f : (generatedArrowCategory edges) _⦋0⦌)
    (hf : Compact.IsKappaCompact.{u, u + 1} κ
      ((generatedArrowInclusion edges).app _ f)) :
    Compact.IsKappaCompact.{u, u + 1} κ f :=
  isKappaCompact_of_fullyFaithful_image (generatedArrowInclusion edges)
    (generatedArrowInclusion_isFullyFaithful edges)
    ((generatedArrowInclusion_preservesSmallColimits hC edges).isKappaAccessibleFunctor κ) f hf

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
