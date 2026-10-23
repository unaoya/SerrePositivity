module

public import SerrePositivity.InfinityCategories.F1B.KanNerveLeftCoconeTransport
public import SerrePositivity.InfinityCategories.F1B.KanNerveColimit
public import SerrePositivity.InfinityCategories.F1B.KanExtensionHom
public import SerrePositivity.InfinityCategories.F1B.KanColimitConstantFamily
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
lemma kanNerveLeftCoconeTransport_isColimit_iff (c : C) :
    IsColimitCone (kanNerveLeftCoconeTransport L β c).cocone ↔
    Nonempty (IsColimit ((Functor.LeftExtension.mk F β).coconeAt c)) := by
  let p := leftKanDiagram (nerveMap L) (nerveMap F₀) (nerveVertex c)
  let j := (kanNerveLeftKanShapeIso L c).hom
  let d := (sliceUnderRestrict p j).app (Opposite.op ⦋0⦌) (kanNerveLeftCoconeTransport L β c).cocone
  have ha : IsColimitCone (kanNerveLeftCoconeTransport L β c).cocone ↔ IsColimitCone d :=
    isInitialVertex_iff_of_isIso (sliceUnderRestrict p j) _
  have hb : IsColimitCone d ↔ IsColimitCone
      (kanNerveCoconeEquiv ((Functor.LeftExtension.mk F β).coconeAt c)) :=
    kanIsColimitCone_congr (kanNerveLeftKanShapeIso_hom_diagram L c F₀) d _
      (kanNerveLeftCoconeTransport_cocone L β c)
  exact ha.trans (hb.trans (kanNerveCocone_isColimit_iff _))

/-- 概要：指定単位の native な左 Kan 条件と通常の pointwise 左 Kan 条件は同値。
方針：局所余錐の厳密な比較、添字同型、余極限性と代表の不変性を合成する。
規約：元の指定単位と拡張関手を保持する。
使われ方：B5 の古典 pointwise 左 Kan の双方向回収。 -/
lemma kanNerve_isLeftKanExtensionHom_iff_pointwise :
    IsLeftKanExtensionHom (nerveMap L) (nerveMap F₀) (nerveMap F)
      (kanNerveNatTransHom (F := F₀) (G := L ⋙ F) β) ↔
        Nonempty (Functor.LeftExtension.mk F β).IsPointwiseLeftKanExtension := by
  rw [isLeftKanExtensionHom_iff_of_representative (nerveMap L) (nerveMap F₀) (nerveMap F)
    (kanNerveNatTransHom (F := F₀) (G := L ⋙ F) β) (kanNerveNatTransHomotopy β)
      (kanNerveNatTransHomotopy_hom β)]
  constructor
  · intro h
    have hc : ∀ c, Nonempty (IsColimit ((Functor.LeftExtension.mk F β).coconeAt c)) := by
      intro c
      obtain ⟨t, ht⟩ := h (nerveVertex c)
      exact (kanNerveLeftCoconeTransport_isColimit_iff L β c).1 ((t.isColimitCone_iff
        (kanNerveLeftCoconeTransport L β c)).1 ht)
    exact ⟨fun c ↦ Classical.choice (hc c)⟩
  · rintro ⟨h⟩ v
    obtain ⟨c, rfl⟩ := (nerveEquiv (C := C)).symm.surjective v
    exact ⟨kanNerveLeftCoconeTransport L β c,
      (kanNerveLeftCoconeTransport_isColimit_iff L β c).2 ⟨h c⟩⟩

end SerrePositivity.InfinityCategories.F1B
