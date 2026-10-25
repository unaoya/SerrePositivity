module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.RelativeSmallPresentationPiece
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageAmbientSmallColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImagePresentations

/-!
概要：実像に属する辺の任意の compact 表示に、実像内の小部分余極限を構成する。
方針：実像側の Yoneda 表示を共終 poset に移し、二表示の相対部分余極限比較を使う。
規約：元の表示と指定種集合を保持。使われ方：三角形表示の一辺を実像へ揃える工程。
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

/-- 実像に属す大域辺の元の表示に、種集合を含む実像内の小部分余極限が存在する。 -/
lemma indArrowImage_exists_smallPartialPiece
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {I : Type u} (edges : I → C _⦋1⦌) (hC : HasSmallColimits C)
    (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hG : IsKappaAccessibleFunctor μ G)
    (hcompact : ∀ a : A _⦋0⦌, IsKappaCompact.{u, u + 1} μ
      ((Ind.indYoneda μ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    (hcol : HasSmallColimits (indArrowImageCategory edges G))
    (hpres : PreservesSmallColimits (indArrowImageInclusion edges G))
    {P₀ : Type u} [PartialOrder P₀] [IsCardinalFiltered P₀ μ]
    [IsKappaFiltered μ (nerve P₀)]
    {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P₀) ⟶
      (ihom (Δ[1] : SSet.{u + 1})).obj C}
    (c₀ : JoinCocone D₀) (hc₀ : IsColimitCone c₀)
    (hD₀ : ∀ i, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i)))
    (hf : IndArrowImageVertex edges G c₀.vertex)
    (seed : Set P₀) (hs : HasCardinalLT seed μ) :
    ∃ P : Set P₀, seed ⊆ P ∧ HasCardinalLT P μ ∧ IsFiltered P ∧
      ∃ a : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (subsetInclusion P)) ≫ D₀),
        IsColimitCone a ∧ IndArrowImageVertex edges G a.vertex := by
  obtain ⟨K, hK, hKμ, b, c, hv, hc⟩ := indArrowImageVertex_hasPresentation edges hC G hG hf
  have := hK
  have := hKμ
  obtain ⟨J, o, q, hJ, hJN, hq⟩ := Ind.exists_cofinal_kappaFiltered_poset (κ := μ) K
  letI := o
  have := hJ
  have := hJN
  let r := (SSet.uliftFunctor.{u + 1, u}).map q
  let H := r ≫ (SSet.uliftFunctor.{u + 1, u}).map b ≫ Ind.indYoneda μ A
  let D₁ := H ≫ G ≫ generatedArrowInclusion edges
  let d := c.restrict r
  have hd : IsColimitCone d :=
    (Ind.isColimitCone_iff_restrict_rightCofinal r (Ind.isRightCofinal_ulift q hq) c).mp hc
  have hvd : d.vertex = c₀.vertex := (JoinCocone.vertex_restrict c r).trans hv
  have hD₁ : ∀ j, IsKappaCompact.{u, u + 1} μ (D₁.app _ (ULift.up j)) :=
    fun j ↦ hcompact (b.app _ (q.app _ j))
  apply exists_relativeSmallPresentationPiece hμ c₀ d hvd.symm
    (functor_hasSmallColimits (Δ[1] : SSet.{u + 1}) hC) hc₀ hd hD₀ hD₁
    (IndArrowImageVertex edges G) (fun e ↦ indArrowImageVertex_iff_vertexIso edges G e)
    (fun J _ E hE a ha ↦ indArrowImage_ambientSmall_colimit_mem
      edges G hcol hpres (nerve J) E hE a ha) ?_ seed hs
  intro k
  exact ⟨H.app _ k, ⟨Iso.refl _⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
