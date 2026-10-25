module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImageCandidates
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPosetColimitCompact

/-!
概要：閉包内の周囲で compact な射は、小さい poset 部分余極限で閉じる。
方針：公開済みの濃度版交換で周囲の compact 性を保ち、元の強飽和閉包の閉性を併用。
規約：濃度変更境界と添字の小ささを明示し、任意の全小余極限閉性とは区別する。
使われ方：HTT 5.5.4.13–14 の小さい部分表示と Ind 像の強飽和性の工程。
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
variable {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)

/-- compact な閉包内の射の小さい poset 部分余極限は、同じ二条件を保持する。 -/
lemma compactGeneratedArrow_smallPosetColimit (h : IsCardinalChangeBound κ μ)
    (J : Type u) [PartialOrder J] (hJ : HasCardinalLT J μ)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ generatedArrowCategory edges)
    (c : JoinCocone (D ≫ generatedArrowInclusion edges)) (hc : IsColimitCone c)
    (hD : ∀ j, Compact.IsKappaCompact.{u, u + 1} μ
      ((D ≫ generatedArrowInclusion edges).app _ j)) :
    Compact.IsKappaCompact.{u, u + 1} μ c.vertex ∧
      arrowVertexEdge c.vertex ∈ generatedEdges edges :=
  ⟨isMuCompact_smallPosetColimit h J hJ c hc hD,
    generatedArrow_colimit_mem edges D c hc⟩

/-- 周囲で compact な閉包内の射の全部分圏は、小さい poset 余極限を実際に持つ。 -/
lemma compactGeneratedArrows_hasSmallPosetColimits (hC : HasSmallColimits C)
    (h : IsCardinalChangeBound κ μ)
    (J : Type u) [PartialOrder J] (hJ : HasCardinalLT J μ)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ compactGeneratedArrows μ edges) :
    HasColimit D := by
  let V : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌ → Prop :=
    Compact.IsKappaCompact.{u, u + 1} μ
  let P := fun f : (Compact.kappaCompactObjects.{u, u + 1} μ
    ((ihom (Δ[1] : SSet.{u + 1})).obj C)) _⦋0⦌ ↦
      arrowVertexEdge f.val ∈ generatedEdges edges
  let j := (fullSubcomplexOnVertices
    (Compact.kappaCompactObjects.{u, u + 1} μ
      ((ihom (Δ[1] : SSet.{u + 1})).obj C)) P).ι
  let E := D ≫ j
  let F := E ≫ Compact.kappaCompactInclusion.{u, u + 1} μ _
  obtain ⟨c, hc⟩ := functor_hasSmallColimits (Δ[1] : SSet.{u + 1}) hC (nerve J) F
  have hcompact : V c.vertex := isMuCompact_smallPosetColimit h J hJ c hc (fun k ↦
    fullSubcomplexOnVertices_vertex (E.app _ k))
  have hmem : arrowVertexEdge c.vertex ∈ generatedEdges edges := by
    apply (stronglySaturatedClosure_stronglySaturated
      (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.1 (nerve J) F c hc
    intro k
    exact fullSubcomplexOnVertices_vertex (D.app _ k)
  let d := Ind.fullCoconeLift V E c hcompact
  have hd := Ind.fullCoconeLift_isColimit V E c hcompact hc
  have hm : P d.vertex := by
    change arrowVertexEdge d.vertex.val ∈ generatedEdges edges
    exact hmem
  exact ⟨Ind.fullCoconeLift P D d hm, Ind.fullCoconeLift_isColimit P D d hm hd⟩

/-- 全 compact 射を含む実像は、小さい compact 部分表示の指定余極限も含む。 -/
lemma indArrowImage_smallCompactPartialColimit
    {A : SSet.{u}} [Quasicategory A] (G : Ind.IndInfinity μ A ⟶ generatedArrowCategory edges)
    (hcover : ∀ f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌,
      Compact.IsKappaCompact.{u, u + 1} μ f →
      arrowVertexEdge f ∈ generatedEdges edges → IndArrowImageVertex edges G f)
    (h : IsCardinalChangeBound κ μ)
    (J : Type u) [PartialOrder J] (hJ : HasCardinalLT J μ)
    (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶ generatedArrowCategory edges)
    (c : JoinCocone (D ≫ generatedArrowInclusion edges)) (hc : IsColimitCone c)
    (hD : ∀ j, Compact.IsKappaCompact.{u, u + 1} μ
      ((D ≫ generatedArrowInclusion edges).app _ j)) :
    IndArrowImageVertex edges G c.vertex := by
  obtain ⟨hcompact, hmem⟩ := compactGeneratedArrow_smallPosetColimit edges h J hJ D c hc hD
  exact hcover c.vertex hcompact hmem

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
