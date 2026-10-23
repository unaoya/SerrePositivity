module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramInitialConeFamily

/-!
概要：指定した評価図式の下で、元の試験族の全始点余錐を構成する。
方針：元の scalar comma の coslice で余錐を取り、点制限に沿って全余錐を持ち上げる。
規約：指定全変換と元の試験族を同時に保持。使われ方：始点評価の cofinal 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の指定評価図式の下で、全試験族の始点余錐を全変換とともに延長する。 -/
lemma exists_diagramComma_initialCone_family_under
    (κ : Cardinal.{u}) [Fact κ.IsRegular] {K C A L : SSet.{u}} [Quasicategory C]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C) (k : K _⦋0⦌)
    (hi : leftAnodyneExtensions (diagramShapePoint k))
    (hA : IsKappaSmall κ A) (hL : IsKappaSmall κ L)
    (z : (SSet.uliftFunctor.{u + 1, u}).obj L ⟶
      leftKanShape (indYoneda κ C) (D.app (Opposite.op ⦋0⦌) (ULift.up k)))
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D)
    (t : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ sliceUnder z)
    (ht : q ≫ diagramCommaEvaluation κ D k = t ≫ sliceUnderProjection z) :
    ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⟶
        pullback (indYoneda κ C) (sliceOverProjection D),
      ∃ P : (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⟶ sliceUnder z,
        (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ G ≫
          diagramConePointRestriction κ D k = q ≫ diagramCommaEvaluation κ D k ∧
        (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ P = t ∧
        G ≫ diagramConePointRestriction κ D k = P ≫ sliceUnderProjection z := by
  have := diagramConePointRestriction_trivialKanFibration κ D k hi
  obtain ⟨s, hs⟩ := trivialKanFibration_exists_section (diagramConePointRestriction κ D k)
  let H := q ≫ diagramCommaEvaluation κ D k ≫ s
  have hH : H ≫ diagramConePointRestriction κ D k = q ≫ diagramCommaEvaluation κ D k := by
    simp only [H, Category.assoc, hs, Category.comp_id]
  obtain ⟨c⟩ := nonempty_indComma_coslice_cocone κ
    (D.app (Opposite.op ⦋0⦌) (ULift.up k)) hL hA z t
  let c₀ : JoinCocone (H ≫ diagramConePointRestriction κ D k) :=
    ⟨c.val ≫ sliceUnderProjection z, by rw [← Category.assoc, c.property, ← ht, hH]⟩
  obtain ⟨d, hd⟩ := exists_cocone_lift_of_trivialKanFibration
    (diagramConePointRestriction κ D k) H c₀
  let G := (uliftCoconeShapeIso.{u, u + 1} A 0).hom ≫ d.val
  let P := (uliftCoconeShapeIso.{u, u + 1} A 0).hom ≫ c.val
  refine ⟨G, P, ?_, ?_, ?_⟩
  · dsimp only [G]
    rw [← Category.assoc _ _ (diagramConePointRestriction κ D k),
      ← Category.assoc, uliftCoconeShapeIso_inl, d.property, hH]
  · dsimp only [P]
    rw [← Category.assoc, uliftCoconeShapeIso_inl, c.property]
  · simpa only [G, P, c₀, Category.assoc] using
      congrArg (fun f ↦ (uliftCoconeShapeIso.{u, u + 1} A 0).hom ≫ f) hd

end SerrePositivity.InfinityCategories.F2.Ind
