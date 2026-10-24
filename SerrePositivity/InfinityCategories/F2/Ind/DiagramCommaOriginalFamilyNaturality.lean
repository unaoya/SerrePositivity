module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaRightPrism

/-!
概要：元の C 全図式を持つ全族は、試験族と図式形状の両制限を厳密に保つ。
方針：元の comma の全射影と内部 Hom の宇宙比較の自然性を照合する。
規約：Yoneda 像での一致で代用せず、元の C 側の全射の等号を示す。
使われ方：二段 slice 持ち上げを元の同じ実 comma の境界へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
  {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D)
/-- 概要：元の C 全族は試験族の任意の制限と厳密に可換。
方針：宇宙比較と全射影の自然性。規約：全係数を保持。使われ方：実 comma の境界。 -/
lemma diagramCommaOriginalFamily_precomp {T₀ : SSet.{u + 1}} (g : T₀ ⟶ T) :
    (g ▷ (SSet.uliftFunctor.{u + 1, u}).obj K) ≫ diagramCommaOriginalFamily κ D q =
      diagramCommaOriginalFamily κ D (g ≫ q) := by
  rw [diagramCommaOriginalFamily, diagramCommaOriginalFamily, ← Category.assoc,
    BraidedCategory.braiding_naturality_left, Category.assoc, ← uncurry_natural_left]
  rfl
/-- 概要：元の C 全族は図式形状の任意の制限と厳密に可換。
方針：宇宙比較と全射影の自然性。規約：全係数を保持。使われ方：実 comma の境界。 -/
lemma diagramCommaOriginalFamily_restrict {J : SSet.{u}} (f : J ⟶ K) :
    (T ◁ (SSet.uliftFunctor.{u + 1, u}).map f) ≫ diagramCommaOriginalFamily κ D q =
      diagramCommaOriginalFamily κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D)
        (q ≫ diagramCommaRestriction κ D f) := by
  have hi : (SSet.uliftFunctor.{u + 1, u}).map ((pre f).app C) ≫
      (uliftFunctorSpaceIso J C).hom = (uliftFunctorSpaceIso K C).hom ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map f)).app
          ((SSet.uliftFunctor.{u + 1, u}).obj C) := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.functorHom_ext
    intro m α
    rfl
  have hx : (q ≫ diagramCommaRestriction κ D f) ≫
      diagramCommaProjection κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D) ≫
        (uliftFunctorSpaceIso J C).hom =
      (q ≫ diagramCommaProjection κ D ≫ (uliftFunctorSpaceIso K C).hom) ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map f)).app
          ((SSet.uliftFunctor.{u + 1, u}).obj C) := by
    have hp := congrArg (fun a ↦ q ≫ a ≫ (uliftFunctorSpaceIso J C).hom)
      (diagramCommaRestriction_projection κ D f)
    simp only [Category.assoc] at hp
    rw [hi] at hp
    simpa only [Category.assoc] using hp
  rw [diagramCommaOriginalFamily, diagramCommaOriginalFamily, ← Category.assoc,
    BraidedCategory.braiding_naturality_right, Category.assoc, ← uncurry_pre_app]
  exact congrArg (fun a ↦ (β_ T ((SSet.uliftFunctor.{u + 1, u}).obj J)).hom ≫ uncurry a) hx.symm
end SerrePositivity.InfinityCategories.F2.Ind
