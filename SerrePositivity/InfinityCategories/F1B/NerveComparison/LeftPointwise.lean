module

public import SerrePositivity.InfinityCategories.F1B.NerveComparison.LeftCoconeTransport
public import SerrePositivity.InfinityCategories.F1B.NerveComparison.Colimit
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Hom
public import SerrePositivity.InfinityCategories.F1B.Cones.ColimitConstantFamily
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceRestrictionIso

/-!
概要：指定単位を伴う左 Kan 条件を通常の pointwise 条件と比較する。
方針：元の指定局所余錐の比較から全頂点の条件を移す。
規約：大域的な Hom 普遍性だけによる Kan 拡張とは区別する。
使われ方：B5 の左 pointwise Kan の古典比較。
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
  (L : K ⥤ C) {F₀ : K ⥤ D} {F : C ⥤ D} (β : F₀ ⟶ L ⋙ F)

/-- 概要：指定単位の native な局所余錐の余極限性と通常の局所余錐の余極限性は同値。
方針：局所余錐の厳密な比較、添字同型、余極限性と代表の不変性を合成する。
規約：元の指定単位と拡張関手を保持する。
使われ方：B5 の古典 pointwise 左 Kan の双方向回収。 -/
lemma nerveLeftCoconeTransport_isColimit_iff (c : C) :
    IsColimitCone (SerrePositivity.InfinityCategories.F1B.nerveLeftCoconeTransport L β c).cocone ↔
    Nonempty (IsColimit ((Functor.LeftExtension.mk F β).coconeAt c)) := by
  let p := leftKanDiagram (nerveMap L) (nerveMap F₀) (nerveVertex c)
  let j := (SerrePositivity.InfinityCategories.F1B.nerveLeftKanShapeIso L c).hom
  let d := (sliceUnderRestrict p j).app (Opposite.op ⦋0⦌) (SerrePositivity.InfinityCategories.F1B.nerveLeftCoconeTransport L β c).cocone
  have ha : IsColimitCone (SerrePositivity.InfinityCategories.F1B.nerveLeftCoconeTransport L β c).cocone ↔ IsColimitCone d :=
    isInitialVertex_iff_of_isIso (sliceUnderRestrict p j) _
  have hb : IsColimitCone d ↔ IsColimitCone
      (SerrePositivity.InfinityCategories.F1B.nerveCoconeEquiv ((Functor.LeftExtension.mk F β).coconeAt c)) :=
    SerrePositivity.InfinityCategories.F1B.isColimitCone_congr (SerrePositivity.InfinityCategories.F1B.nerveLeftKanShapeIso_hom_diagram L c F₀) d _
      (SerrePositivity.InfinityCategories.F1B.nerveLeftCoconeTransport_cocone L β c)
  exact ha.trans (hb.trans (SerrePositivity.InfinityCategories.F1B.nerveCocone_isColimit_iff _))

/-- 概要：指定単位の native な左 Kan 条件と通常の pointwise 左 Kan 条件は同値。
方針：局所余錐の厳密な比較、添字同型、余極限性と代表の不変性を合成する。
規約：元の指定単位と拡張関手を保持する。
使われ方：B5 の古典 pointwise 左 Kan の双方向回収。 -/
lemma nerve_isLeftKanExtensionHom_iff_pointwise :
    IsLeftKanExtensionHom (nerveMap L) (nerveMap F₀) (nerveMap F)
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHom (F := F₀) (G := L ⋙ F) β) ↔
        Nonempty (Functor.LeftExtension.mk F β).IsPointwiseLeftKanExtension := by
  rw [isLeftKanExtensionHom_iff_of_representative (nerveMap L) (nerveMap F₀) (nerveMap F)
    (SerrePositivity.InfinityCategories.F1B.nerveNatTransHom (F := F₀) (G := L ⋙ F) β) (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy β)
      (SerrePositivity.InfinityCategories.F1B.nerveNatTransHomotopy_hom β)]
  constructor
  · intro h
    have hc : ∀ c, Nonempty (IsColimit ((Functor.LeftExtension.mk F β).coconeAt c)) := by
      intro c
      obtain ⟨t, ht⟩ := h (nerveVertex c)
      exact (nerveLeftCoconeTransport_isColimit_iff L β c).1 ((t.isColimitCone_iff
        (SerrePositivity.InfinityCategories.F1B.nerveLeftCoconeTransport L β c)).1 ht)
    exact ⟨fun c ↦ Classical.choice (hc c)⟩
  · rintro ⟨h⟩ v
    obtain ⟨c, rfl⟩ := (nerveEquiv (C := C)).symm.surjective v
    exact ⟨SerrePositivity.InfinityCategories.F1B.nerveLeftCoconeTransport L β c,
      (nerveLeftCoconeTransport_isColimit_iff L β c).2 ⟨h c⟩⟩

end SerrePositivity.InfinityCategories.F1B
