module
public import SerrePositivity.InfinityCategories.Core.Cocone

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCoconeIso
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes

/-!
概要：補間領域上の実余錐を元の二つの余錐の積へ戻す。
方針：構成した実同型の逆と余錐形状の宇宙同型で前合成する。
規約：任意の元の両形状と全境界を保持し、有限性を要求しない。
使われ方：有限半順序形状の点追加における相対補間。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
universe v
/-- 概要：補間領域上の実余錐を元の二つの余錐の積へ戻す。
方針：構成した実同型の逆と余錐形状の宇宙同型で前合成する。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
noncomputable def coneTensorExtend {A L : SSet.{u}} {X : SSet.{max u v}}
    {H : (SSet.uliftFunctor.{v, u}).obj (coneTensorCorner A L) ⟶ X}
    (c : JoinCocone H) :
    (SSet.uliftFunctor.{v, u}).obj (join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0]) ⟶ X :=
  (SSet.uliftFunctor.{v, u}).map (coneTensorCoconeIso A L).inv ≫
    (uliftCoconeShapeIso.{u, v} (coneTensorCorner A L) 0).hom ≫ c.val
/-- 概要：補間領域上の実余錐を元の二つの余錐の積へ戻す。
方針：構成した実同型の逆と余錐形状の宇宙同型で前合成する。
規約：元の全射を保持。使われ方：点追加の相対補間。 -/
lemma coneTensorExtend_inclusion {A L : SSet.{u}} {X : SSet.{max u v}}
    {H : (SSet.uliftFunctor.{v, u}).obj (coneTensorCorner A L) ⟶ X}
    (c : JoinCocone H) :
    (SSet.uliftFunctor.{v, u}).map (coneTensorCornerInclusion A L) ≫ coneTensorExtend c = H := by
  have hi : coneTensorCornerInclusion A L ≫ (coneTensorCoconeIso A L).inv =
      joinInl (coneTensorCorner A L) (Δ[0] : SSet.{u}) := by
    apply (cancel_mono (coneTensorCoconeIso A L).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (coneTensorCocone_inl A L).symm
  rw [coneTensorExtend, ← Category.assoc, ← Functor.map_comp, hi,
    ← Category.assoc, uliftCoconeShapeIso_inl]
  exact c.property


end SerrePositivity.InfinityCategories.F2.Ind
