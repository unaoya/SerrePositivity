module

public import SerrePositivity.InfinityCategories.F2.Presentable.CoherentPosetLimitExchange
public import SerrePositivity.InfinityCategories.F2.Ind.FilteredPosetNerve
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift

/-!
概要：小さい poset の極限と、一般の μ-filtered ∞ 添字の coherent な指定点ごとの余極限の交換。
方針：元の全余錐を cofinal μ-filtered poset へ制限し、通常添字での実証済み交換へ渡す。
規約：元の指定頂点と全錐を保持し、交換を仮定や instance で補わない。
使われ方：μ-small な κ-filtered 部分余極限の μ-compact 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の点ごとの余極限余錐の cofinal 制限は、同じ全評価で余極限である。 -/
lemma pointwiseColimitCocone_restrict_rightCofinal {A B K X : SSet.{u}}
    [Quasicategory B] [Quasicategory X]
    {p : B ⟶ (ihom K).obj X} (c : JoinCocone p) (hc : IsPointwiseColimitCone c)
    (r : A ⟶ B) (hr : IsRightCofinal r) : IsPointwiseColimitCone (c.restrict r) := by
  intro k
  have h := (Ind.isColimitCone_iff_restrict_rightCofinal r hr
    (evaluateFunctorCocone c k)).mp (hc k)
  exact (isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _)).mpr h

/-- 元の一般の μ-filtered ∞ 添字の全錐族の指定点ごとの余極限は、同じ poset 形状の極限を保つ。 -/
lemma coherentCardinalFilteredLimitExchange_poset
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ) (I : Type u) [PartialOrder I] (hI : HasCardinalLT I μ)
    (B : SSet.{u}) [Quasicategory B] [IsKappaFiltered μ B]
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶
      (ihom (join (Δ[0] : SSet.{u + 1})
        ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj SpaceInfinity.{u})
    (c : JoinCocone F) (hc : IsPointwiseColimitCone c)
    (hF : ∀ b : B _⦋0⦌, IsLimitCone (functorVertexCone (F.app
      (Opposite.op ⦋0⦌) (ULift.up b)))) : IsLimitCone (functorVertexCone c.vertex) := by
  obtain ⟨J, o, f, hJ, _, hf⟩ := Ind.exists_cofinal_kappaFiltered_poset (κ := μ) B
  let := o
  have := hJ
  let r := (SSet.uliftFunctor.{u + 1, u}).map f
  have hcJ := pointwiseColimitCocone_restrict_rightCofinal c hc r
    (Ind.isRightCofinal_ulift f hf)
  have ht := coherentCardinalFilteredLimitExchange_nerve_poset h I hI J
    (r ≫ F) (c.restrict r) hcJ
    (fun j ↦ hF (f.app (Opposite.op ⦋0⦌) (nerveVertex j)))
  rwa [JoinCocone.vertex_restrict] at ht

end SerrePositivity.InfinityCategories.F2.Presentable
