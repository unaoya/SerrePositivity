module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompatiblePieceProjections
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPartialColimitPresentation
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPosetColimitCompactUniverse

/-!
概要：元の部分余極限表示を、共終な同時細分添字へ制限する。
方針：公開の coherent な部分余極限族を共終写像で制限し、同じ大域頂点を回収する。
規約：各値の部分余錐とその厳密な頂点を保持。使われ方：比較可能な対での両側の表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact
local instance : Fact Cardinal.aleph0.IsRegular := ⟨Cardinal.isRegular_aleph0⟩

/-- 共終な部分表示族の上でも、元の全余極限頂点と各値の実部分余錐を回収する。 -/
lemma exists_cofinalSmallPartialColimitFamily
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : Type u} [PartialOrder I] [IsCardinalFiltered I Cardinal.aleph0.{u}]
    {C : SSet.{u + 1}} [Quasicategory C] (hC : HasSmallColimits C)
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ C}
    (c : JoinCocone D) (hc : IsColimitCone c)
    {B : Type u} [Preorder B]
    {p : B → SmallFilteredPieces Cardinal.aleph0 μ I} (hp : Monotone p)
    (hcof : IsRightCofinal (nerveMap hp.functor)) :
    ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve B) ⟶ C,
      (∀ b, ∃ a : JoinCocone (smallFilteredPartialDiagram D (p b)),
        IsColimitCone a ∧ a.vertex = F.app _ (ULift.up (nerveVertex b))) ∧
      ∃ d : JoinCocone F, IsColimitCone d ∧ d.vertex = c.vertex := by
  obtain ⟨G, β, _, _, hG, d, hd, hv⟩ := exists_smallPartialColimitPresentation
    (cardinalChangeBound_aleph0 hμ) (hC.hasSmallKappaFilteredColimits Cardinal.aleph0) c hc
  let q := (SSet.uliftFunctor.{u + 1, u}).map (nerveMap hp.functor)
  refine ⟨q ≫ G, ?_, d.restrict q, ?_, ?_⟩
  · intro b
    obtain ⟨a, ha, hav⟩ := hG (p b)
    exact ⟨a, ha, hav⟩
  · exact (Ind.isColimitCone_iff_restrict_rightCofinal q
      (Ind.isRightCofinal_ulift _ hcof) d).mp hd
  · exact (JoinCocone.vertex_restrict d q).trans hv

/-- 各部分表示の compact な段と小ささから、同じ族の値は μ-compact。 -/
lemma cofinalSmallPartialColimitFamily_values_compact
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : Type u} [PartialOrder I]
    {C : SSet.{u + 1}} [Quasicategory C]
    {D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ C}
    (hD : ∀ k, IsKappaCompact.{u, u + 1} μ (D.app (Opposite.op ⦋0⦌) k))
    {B : Type u} [Preorder B] (p : B → SmallFilteredPieces Cardinal.aleph0 μ I)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve B) ⟶ C)
    (hF : ∀ b, ∃ a : JoinCocone (smallFilteredPartialDiagram D (p b)),
      IsColimitCone a ∧ a.vertex = F.app _ (ULift.up (nerveVertex b))) :
    ∀ k, IsKappaCompact.{u, u + 1} μ (F.app (Opposite.op ⦋0⦌) k) := by
  rintro ⟨k⟩
  obtain ⟨b, rfl⟩ := nerveEquiv.symm.surjective k
  obtain ⟨a, ha, hv⟩ := hF b
  have h := isKappaCompact_smallPosetColimit_universe hμ (p b).val (p b).property.2 a ha
    (fun k ↦ hD (((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (subsetInclusion (p b).val))).app _ k))
  rw [hv] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
