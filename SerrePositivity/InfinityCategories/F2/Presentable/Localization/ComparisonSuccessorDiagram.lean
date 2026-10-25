module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactCoconeVertices
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalCoconeRestriction

/-!
概要：左側の後続因子化の全余錐を次の小さい全比較図式へ正規化する。
方針：coslice の宇宙同型と join の自然性で元の両添字図式を厳密に回収する。
規約：増大余錐の整合とは独立の、全図式の等式を証明する。
使われ方：HTT 5.5.4.13 の交互後続状態。
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

/-- 余錐形状の宇宙同型は、元の全前置形状の写像と可換。 -/
lemma uliftCoconeShapeIso_left_naturality {K L : SSet.{u}} (i : K ⟶ L) :
    (SSet.uliftFunctor.{u + 1, u}).map (joinMap i (𝟙 Δ[0])) ≫
      (uliftCoconeShapeIso.{u, u + 1} L 0).hom =
    (uliftCoconeShapeIso.{u, u + 1} K 0).hom ≫
      joinMap ((SSet.uliftFunctor.{u + 1, u}).map i) (𝟙 Δ[0]) := by
  unfold uliftCoconeShapeIso
  simp only [Iso.trans_hom, joinIso, Iso.refl_hom]
  rw [← Category.assoc, uliftJoinIso_hom_naturality]
  simp only [Category.assoc]
  rw [← joinMap_comp, ← joinMap_comp, (SSet.uliftFunctor.{u + 1, u}).map_id]
  simp only [Category.id_comp, Category.comp_id]

variable {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
  {D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C}
  {D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C}
  {c₀ : JoinCocone D₀} {c₁ : JoinCocone D₁}

/-- 左側の後続表示の全単体値は、元の同じ添字余錐の持ち上げ・後合成。 -/
lemma comparisonLeftStages_val (s : CompactPresentationComparison μ D₀ D₁ c₀ c₁)
    {n : ℕ} (j : (sliceUnder s.left_index) _⦋n⦌) :
    ((comparisonLeftStages s).app _ (ULift.up j)).val =
      (uliftCoconeShapeIso.{u, u + 1} s.left_shape n).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map j.val ≫ D₀ := by
  dsimp only [comparisonLeftStages, NatTrans.comp_app, types_comp_apply]
  rw [Ind.sliceUnder_eqToIso_val s.left_diagram.symm]
  change (((uliftSliceUnderIso.{u, u + 1} s.left_index).hom.app _ (ULift.up j)).val ≫ D₀) = _
  rw [uliftSliceUnderIso_hom_val, Category.assoc]

/-- 後続として加わる余錐全体を、次の小さい形状の全図式として読む。 -/
def comparisonSuccessorDiagram {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s) :
    (SSet.uliftFunctor.{u + 1, u}).obj (join s.shape Δ[0]) ⟶ C :=
  (uliftCoconeShapeIso.{u, u + 1} s.shape 0).hom ≫ f.cocone.val

/-- 次の全図式の全頂点は、元の同じ compact 濃度を保つ。 -/
lemma comparisonSuccessorDiagram_compact {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s)
    (hD : ∀ i : I₀ _⦋0⦌, IsKappaCompact.{u, u + 1} μ (D₀.app _ (ULift.up i))) :
    ∀ v, IsKappaCompact.{u, u + 1} μ ((comparisonSuccessorDiagram f).app _ v) :=
  fun v ↦ f.cocone_compact hD ((uliftCoconeShapeIso.{u, u + 1} s.shape 0).hom.app _ v)

/-- 左側の新しい全前置図式は、元の同じ左表示の添字余錐そのもの。 -/
lemma comparisonSuccessorDiagram_left {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s) :
    (SSet.uliftFunctor.{u + 1, u}).map (joinMap s.left_inclusion (𝟙 Δ[0])) ≫
      comparisonSuccessorDiagram f =
        (SSet.uliftFunctor.{u + 1, u}).map f.index.val ≫ D₀ := by
  dsimp only [comparisonSuccessorDiagram]
  rw [← Category.assoc, uliftCoconeShapeIso_left_naturality, Category.assoc]
  change (uliftCoconeShapeIso.{u, u + 1} s.left_shape 0).hom ≫
    (f.cocone.restrict ((SSet.uliftFunctor.{u + 1, u}).map s.left_inclusion)).val = _
  rw [f.prefix_eq, comparisonLeftStages_val, Iso.hom_inv_id_assoc]

/-- 右側の旧全前置図式は、次の同じ全比較図式の中に厳密に残る。 -/
lemma comparisonSuccessorDiagram_right {s : CompactPresentationComparison μ D₀ D₁ c₀ c₁}
    (f : ComparisonLeftFactor s) :
    (SSet.uliftFunctor.{u + 1, u}).map (s.right_inclusion ≫ joinInl s.shape Δ[0]) ≫
      comparisonSuccessorDiagram f =
        (SSet.uliftFunctor.{u + 1, u}).map s.right_index ≫ D₁ := by
  dsimp only [comparisonSuccessorDiagram]
  rw [(SSet.uliftFunctor.{u + 1, u}).map_comp, Category.assoc,
    ← Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map (joinInl s.shape Δ[0])),
    uliftCoconeShapeIso_inl, f.cocone.property, s.right_diagram]

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
