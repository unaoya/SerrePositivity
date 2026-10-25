module

public import SerrePositivity.InfinityCategories.F2.Ind.PosetLowerSubsetCoconeLift
public import SerrePositivity.InfinityCategories.F2.Ind.EmptyDiagramPresentation

/-!
概要：元の有限半順序図式の同じ表示 comma は κ-filtered である。
方針：空の下方部分の全余錐を、有限半順序の厳密な指定余錐持ち上げで戻す。
規約：元の全図式・元の全試験族・小さい表示模型を保持する。
使われ方：I-2 a④ の有限半順序形状の単一 filtered 表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) [Fact κ.IsRegular] {P : Type u} [PartialOrder P] [Finite P]
  {C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ IndInfinity κ C)

/-- 概要：元の有限半順序図式の表示 comma の任意の小さい全族に実余錐がある。
方針：空の固定部分から持ち上げ。規約：元の q。使われ方：filtered 性の判定。 -/
lemma nonempty_finitePosetDiagramComma_cocone {A : SSet.{u}} (hA : IsKappaSmall κ A)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D) :
    Nonempty (JoinCocone q) := by
  let r := nerveMap (OrderHom.Subtype.val (∅ : Set P)).toFunctor
  have hK : ¬ (nerve {p : P // p ∈ (∅ : Set P)}).Nonempty := by
    rintro ⟨k⟩
    exact (nerveEquiv k).property
  obtain ⟨G⟩ := nonempty_emptyDiagramComma_cocone κ
    ((SSet.uliftFunctor.{u + 1, u}).map r ≫ D) hK (q ≫ diagramCommaRestriction κ D r)
  obtain ⟨c, _⟩ := exists_diagramComma_cocone_lift_poset_lowerSet κ (∅ : Set P)
    (by intro x y hxy hy; exact False.elim hy) D hA q G
  exact ⟨c⟩

/-- 概要：元の有限半順序全図式の小さい実表示 comma は κ-filtered。
方針：元の全族の余錐を小さい模型へ降ろす。
規約：同じ表示添字。使われ方：標準全余錐による単一表示。 -/
lemma smallFinitePosetDiagramComma_isKappaFiltered :
    IsKappaFiltered κ (smallDiagramComma κ D) := by
  constructor
  intro A hA f
  let q := (SSet.uliftFunctor.{u + 1, u}).map f ≫ (smallDiagramCommaIso κ D).hom
  obtain ⟨c⟩ := nonempty_finitePosetDiagramComma_cocone κ D hA q
  have hc : JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map f) := by
    simpa only [q, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      mapJoinCocone (smallDiagramCommaIso κ D).inv c
  obtain ⟨d, _⟩ := JoinCocone.ulift_surjective.{u, u + 1} f hc
  exact ⟨d⟩

end SerrePositivity.InfinityCategories.F2.Ind
