module

public import SerrePositivity.InfinityCategories.F1B.KanNerveRightConeTransport
public import SerrePositivity.InfinityCategories.F1B.KanNerveLimit
public import SerrePositivity.InfinityCategories.F1B.KanExtensionHom
public import SerrePositivity.InfinityCategories.F1B.KanRightConstantFamily

/-!
概要：指定余単位を伴う右 Kan 条件を通常の pointwise 条件と比較する。
方針：元の指定局所錐の比較から全頂点の条件を移す。
規約：大域的な Hom 普遍性だけによる Kan 拡張とは区別する。
使われ方：B5 の右 pointwise Kan の古典比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

variable {K C D : Type u} [Category.{u} K] [Category.{u} C] [Category.{u} D]
  (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (α : L ⋙ F ⟶ F₀)

/-- 概要：指定余単位の native な局所錐の極限性と通常の局所錐の極限性は同値。
方針：局所錐の厳密な比較、添字同型、極限性と代表の不変性を合成する。
規約：元の指定余単位と拡張関手を保持する。
使われ方：B5 の古典 pointwise 右 Kan の双方向回収。 -/
lemma kanNerveRightConeTransport_isLimit_iff (c : C) :
    IsLimitCone (kanNerveRightConeTransport L α c).cone ↔
    Nonempty (IsLimit ((Functor.RightExtension.mk F α).coneAt c)) := by
  let p := rightKanDiagram (nerveMap L) (nerveMap F₀) (nerveVertex c)
  let j := (kanNerveRightKanShapeIso c L).hom
  let d := (sliceOverRestrict p j).app (Opposite.op ⦋0⦌) (kanNerveRightConeTransport L α c).cone
  have := sliceOverRestrict_isIso p j
  have ha : IsLimitCone (kanNerveRightConeTransport L α c).cone ↔ IsLimitCone d :=
    ⟨fun h ↦ h.map_of_isIso _, fun h ↦ isTerminalVertex_of_trivialKanFibration _ h⟩
  have hb : IsLimitCone d ↔ IsLimitCone (kanNerveCone ((Functor.RightExtension.mk F α).coneAt c)) :=
    kanIsLimitCone_congr (kanNerveRightKanShapeIso_hom_diagram c L F₀) d _
      (kanNerveRightConeTransport_cone L α c)
  exact ha.trans (hb.trans (kanNerveCone_isLimit_iff _))

/-- 概要：指定余単位の native な右 Kan 条件と通常の pointwise 右 Kan 条件は同値。
方針：局所錐の厳密な比較、添字同型、極限性と代表の不変性を合成する。
規約：元の指定余単位と拡張関手を保持する。
使われ方：B5 の古典 pointwise 右 Kan の双方向回収。 -/
lemma kanNerve_isRightKanExtensionHom_iff_pointwise :
    IsRightKanExtensionHom (nerveMap L) (nerveMap F₀) (nerveMap F)
      (kanNerveNatTransHom (F := L ⋙ F) (G := F₀) α) ↔
        Nonempty (Functor.RightExtension.mk F α).IsPointwiseRightKanExtension := by
  rw [isRightKanExtensionHom_iff_of_representative (nerveMap L) (nerveMap F₀) (nerveMap F)
    (kanNerveNatTransHom (F := L ⋙ F) (G := F₀) α) (kanNerveNatTransHomotopy α)
      (kanNerveNatTransHomotopy_hom α)]
  constructor
  · intro h
    have hc : ∀ c, Nonempty (IsLimit ((Functor.RightExtension.mk F α).coneAt c)) := by
      intro c
      obtain ⟨t, ht⟩ := h (nerveVertex c)
      exact (kanNerveRightConeTransport_isLimit_iff L α c).1 ((t.isLimitCone_iff
        (kanNerveRightConeTransport L α c)).1 ht)
    exact ⟨fun c ↦ Classical.choice (hc c)⟩
  · rintro ⟨h⟩ v
    obtain ⟨c, rfl⟩ := (nerveEquiv (C := C)).symm.surjective v
    exact ⟨kanNerveRightConeTransport L α c, (kanNerveRightConeTransport_isLimit_iff L α c).2 ⟨h c⟩⟩

end SerrePositivity.InfinityCategories.F1B
