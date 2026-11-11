module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MapHomotopyCategoryComp
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UniverseHomotopyDownNaturality

/-!
概要：縮小・下降・後合成を、持ち上げた単一の写像と下降による同じ通常の関手へ表示する。
方針：下降の自然性とホモトピー圏の関手性で、表示同型の往復を相殺する。
規約：対象と全射への作用を同時に保持。使われ方：指定 path の合成と端点補正の同時比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v w z
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 下降前後の後合成は同じ一つの通常の関手を与える。 -/
lemma universeHomotopyDown_post_functor {R T : SSet.{u}} {X : SSet.{max u v}}
    (g : X ⟶ (SSet.uliftFunctor.{v, u}).obj R) (Q : R ⟶ T) :
    SSet.mapHomotopyCategory g ⋙ universeHomotopyDown R ⋙ SSet.mapHomotopyCategory Q =
      SSet.mapHomotopyCategory (g ≫ (SSet.uliftFunctor.{v, u}).map Q) ⋙
        universeHomotopyDown T := by
  rw [universeHomotopyDown_naturality, mapHomotopyCategory_comp_eq]
  rfl

/-- 表示同型の往復を相殺し、対象・全射で同じ下降関手を回収する。 -/
lemma universeHomotopyDown_post_functor_iso_cancel {R T : SSet.{u}}
    {X U : SSet.{max u v}} (g : X ⟶ (SSet.uliftFunctor.{v, u}).obj R) (Q : R ⟶ T)
    (E : (SSet.uliftFunctor.{v, u}).obj T ≅ U) :
    SSet.mapHomotopyCategory g ⋙ universeHomotopyDown R ⋙ SSet.mapHomotopyCategory Q =
      SSet.mapHomotopyCategory (g ≫ (SSet.uliftFunctor.{v, u}).map Q ≫ E.hom) ⋙
        SSet.mapHomotopyCategory E.inv ⋙ universeHomotopyDown T := by
  rw [universeHomotopyDown_post_functor, ← Functor.assoc,
    ← mapHomotopyCategory_comp_eq]
  simp only [Category.assoc, E.hom_inv_id, Category.comp_id]

/-- 異なる宇宙の通常の圏の間でも、関手の等式は指定同型の像を保持する。 -/
lemma mapIso_heq_of_functor_eq_levels {C : Type u} {D : Type v}
    [Category.{w} C] [Category.{z} D] {P Q : C ⥤ D}
    (h : P = Q) {a b : C} (e : a ≅ b) : HEq (P.mapIso e) (Q.mapIso e) := by
  cases h
  rfl

end SerrePositivity.InfinityCategories.F2
