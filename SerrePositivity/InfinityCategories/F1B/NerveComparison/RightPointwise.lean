module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.RightConeTransport
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.Limit
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Hom
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RightConstantFamily

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
lemma nerveRightConeTransport_isLimit_iff (c : C) :
    IsLimitCone (SerrePositivity.InfinityCategories.F1B.nerveRightConeTransport L α c).cone ↔
    Nonempty (IsLimit ((Functor.RightExtension.mk F α).coneAt c)) := by
  let p := rightKanDiagram (nerveMap L) (nerveMap F₀) (nerveVertex c)
  let j := (SerrePositivity.InfinityCategories.F1B.nerveRightKanShapeIso c L).hom
  let d := (sliceOverRestrict p j).app (Opposite.op ⦋0⦌) (SerrePositivity.InfinityCategories.F1B.nerveRightConeTransport L α c).cone
  have := sliceOverRestrict_isIso p j
  have ha : IsLimitCone (SerrePositivity.InfinityCategories.F1B.nerveRightConeTransport L α c).cone ↔ IsLimitCone d :=
    ⟨fun h ↦ h.map_of_isIso _, fun h ↦ isTerminalVertex_of_trivialKanFibration _ h⟩
  have hb : IsLimitCone d ↔ IsLimitCone (SerrePositivity.InfinityCategories.F1B.nerveCone ((Functor.RightExtension.mk F α).coneAt c)) :=
    kanIsLimitCone_congr (SerrePositivity.InfinityCategories.F1B.nerveRightKanShapeIso_hom_diagram c L F₀) d _
      (SerrePositivity.InfinityCategories.F1B.nerveRightConeTransport_cone L α c)
  exact ha.trans (hb.trans (SerrePositivity.InfinityCategories.F1B.nerveCone_isLimit_iff _))

/-- 概要：指定余単位の native な右 Kan 条件と通常の pointwise 右 Kan 条件は同値。
方針：局所錐の厳密な比較、添字同型、極限性と代表の不変性を合成する。
規約：元の指定余単位と拡張関手を保持する。
使われ方：B5 の古典 pointwise 右 Kan の双方向回収。 -/
lemma nerve_isRightKanExtensionHom_iff_pointwise :
    IsRightKanExtensionHom (nerveMap L) (nerveMap F₀) (nerveMap F)
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHom (F := L ⋙ F) (G := F₀) α) ↔
        Nonempty (Functor.RightExtension.mk F α).IsPointwiseRightKanExtension := by
  rw [isRightKanExtensionHom_iff_of_representative (nerveMap L) (nerveMap F₀) (nerveMap F)
    (SerrePositivity.InfinityCategories.F1B.nerveNatTransHom (F := L ⋙ F) (G := F₀) α) (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy α)
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy_hom α)]
  constructor
  · intro h
    have hc : ∀ c, Nonempty (IsLimit ((Functor.RightExtension.mk F α).coneAt c)) := by
      intro c
      obtain ⟨t, ht⟩ := h (nerveVertex c)
      exact (nerveRightConeTransport_isLimit_iff L α c).1 ((t.isLimitCone_iff
        (SerrePositivity.InfinityCategories.F1B.nerveRightConeTransport L α c)).1 ht)
    exact ⟨fun c ↦ Classical.choice (hc c)⟩
  · rintro ⟨h⟩ v
    obtain ⟨c, rfl⟩ := (nerveEquiv (C := C)).symm.surjective v
    exact ⟨SerrePositivity.InfinityCategories.F1B.nerveRightConeTransport L α c, (nerveRightConeTransport_isLimit_iff L α c).2 ⟨h c⟩⟩

end SerrePositivity.InfinityCategories.F1B
