module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageMappedRelativePiece
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.TriangleFaces

/-!
概要：三角形の一辺が実像に属せば、任意の種集合を含む実部分三角形を同じ条件へ細分する。
方針：辺への余極限保存制限に相対部分表示を適用し、三辺の compact 性も回収する。
規約：他の辺の実像所属はまだ主張しない。使われ方：二辺を交互に揃える同時細分。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 三辺が compact な実部分三角形で、一つの指定辺が実像に属するもの。 -/
structure TriangleFacePartialRefinement (μ : Cardinal.{u})
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    {J : Type u} [PartialOrder J]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
      (ihom (Δ[2] : SSet.{u + 1})).obj C) (j : Fin 3) (seed : Set J) where
  piece : Set J
  seed_subset : seed ⊆ piece
  small : HasCardinalLT piece μ
  filtered : IsFiltered piece
  cocone : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (subsetInclusion piece)) ≫ D)
  colimit : IsColimitCone cocone
  compact : IsKappaCompact.{u, u + 1} μ cocone.vertex
  faces_compact : ∀ k : Fin 3, IsKappaCompact.{u, u + 1} μ
    (((pre (stdSimplex.δ k)).app C).app _ cocone.vertex)
  face_mem : IndArrowImageVertex edges G (((pre (stdSimplex.δ j)).app C).app _ cocone.vertex)

/-- 元の全三角形表示の一辺を、任意の種集合を保って実像へ揃えられる。 -/
lemma nonempty_triangleFacePartialRefinement
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcol : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (indArrowImageCategory edges G))
    (hpres : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (indArrowImageInclusion edges G))
    {J : Type u} [PartialOrder J] [IsCardinalFiltered J μ] [IsKappaFiltered μ (nerve J)]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
      (ihom (Δ[2] : SSet.{u + 1})).obj C}
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD : ∀ k, IsKappaCompact.{u, u + 1} μ (D.app _ k))
    (hfaces : ∀ k (l : Fin 3), IsKappaCompact.{u, u + 1} μ
      (((pre (stdSimplex.δ l)).app C).app _ (D.app _ k)))
    (j : Fin 3) (hf : IndArrowImageVertex edges G (((pre (stdSimplex.δ j)).app C).app _ c.vertex))
    (seed : Set J) (hs : HasCardinalLT seed μ) :
    Nonempty (TriangleFacePartialRefinement μ edges G D j seed) := by
  obtain ⟨P, hseed, hsmall, hfiltered, a, ha, hm⟩ :=
    indArrowImage_exists_mappedSmallPartialPiece hμ edges hC G hG hcompact hcol hpres
      (functor_hasSmallColimits (Δ[2] : SSet.{u + 1}) hC)
      ((pre (stdSimplex.δ j)).app C) (triangleFace_preservesSmallColimits hC j)
      c hc (fun k ↦ hfaces (ULift.up k) j) hf seed hs
  let r := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap (subsetInclusion P))
  have hcomp : IsKappaCompact.{u, u + 1} μ a.vertex :=
    isKappaCompact_smallPosetColimit_universe hμ P hsmall a ha
      (fun k ↦ hD (r.app _ k))
  refine ⟨⟨P, hseed, hsmall, hfiltered, a, ha, hcomp, ?_, hm⟩⟩
  intro l
  have hfa := triangleFace_preservesSmallColimits hC l (nerve P) (r ≫ D) a ha
  have h := isKappaCompact_smallPosetColimit_universe hμ P hsmall
    (mapJoinCocone ((pre (stdSimplex.δ l)).app C) a) hfa
    (fun k ↦ hfaces (r.app _ k) l)
  rw [Ind.mapJoinCocone_vertex] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
