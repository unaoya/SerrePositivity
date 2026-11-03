module
public import SerrePositivity.InfinityCategories.Core.Cocone

public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationCoconeSurjective
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes
public import SerrePositivity.InfinityCategories.Core.Slice

/-!
概要：補間領域の実余錐を同じ全円柱上の全図式へ戻す。
方針：全円柱同型の逆と余錐形状の宇宙同型で前合成する。
規約：元の補間図式全体を厳密に保持。使われ方：射図式の二段表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 補間領域の実余錐から、元の全円柱上の図式を作る。 -/
def arrowInterpolationExtend {A : SSet.{u}} {X : SSet.{max u v}}
    {H : (SSet.uliftFunctor.{v, u}).obj (arrowInterpolationCorner A) ⟶ X}
    (c : JoinCocone H) :
    (SSet.uliftFunctor.{v, u}).obj (join A (Δ[0] : SSet.{u}) ⊗ Δ[1]) ⟶ X :=
  (SSet.uliftFunctor.{v, u}).map (arrowInterpolationCoconeIso A).inv ≫
    (uliftCoconeShapeIso.{u, v} (arrowInterpolationCorner A) 0).hom ≫ c.val

/-- 全円柱に戻した図式は、元の補間図式全体に厳密に制限される。 -/
lemma arrowInterpolationExtend_inclusion {A : SSet.{u}} {X : SSet.{max u v}}
    {H : (SSet.uliftFunctor.{v, u}).obj (arrowInterpolationCorner A) ⟶ X}
    (c : JoinCocone H) :
    (SSet.uliftFunctor.{v, u}).map (arrowInterpolationCornerInclusion A) ≫
      arrowInterpolationExtend c = H := by
  have hi : arrowInterpolationCornerInclusion A ≫ (arrowInterpolationCoconeIso A).inv =
      joinInl (arrowInterpolationCorner A) (Δ[0] : SSet.{u}) := by
    calc
      _ = (joinInl (arrowInterpolationCorner A) Δ[0] ≫
          (arrowInterpolationCoconeIso A).hom) ≫ (arrowInterpolationCoconeIso A).inv := by
        rw [show (arrowInterpolationCoconeIso A).hom = arrowInterpolationCocone A from rfl,
          arrowInterpolationCocone_inl]
      _ = _ := by rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [arrowInterpolationExtend, ← Category.assoc, ← Functor.map_comp, hi,
    ← Category.assoc, uliftCoconeShapeIso_inl]
  exact c.property

end SerrePositivity.InfinityCategories.F2.Ind
