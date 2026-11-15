module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
概要：実際の Čech nerve の自然な射は、Cartesian な Arrow の射で基底変更となる。
方針：同じ元の Cartesian square と finite wide pullback の普遍性を使う。
規約：既存の mapCechNerve と増大項への base をそのまま保持する。
使われ方：同じ閉中心の nerve と元の nerve の各項の底変換を自然に照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- Cartesian な Arrow の射からの実際の nerve の射は、各項で同じ底変換。 -/
theorem isPullback_cechNerve_base {f g : Arrow C} (F : f ⟶ g)
    (H : IsPullback F.left f.hom g.hom F.right) (n : SimplexCategoryᵒᵖ) :
    IsPullback ((Arrow.mapCechNerve F).app n)
      (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f.hom))
      (WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ g.hom)) F.right := by
  have hw : (Arrow.mapCechNerve F).app n ≫
      WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ g.hom) =
      WidePullback.base (fun _ : Fin (n.unop.len + 1) ↦ f.hom) ≫ F.right := by
    simp only [Arrow.mapCechNerve_app, WidePullback.lift_base]
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk hw ?_ ?_ ?_ ?_⟩⟩
  · intro c
    exact WidePullback.lift c.snd
      (fun j : Fin (n.unop.len + 1) ↦ H.lift
        (c.fst ≫ WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ g.hom) j) c.snd
        (by rw [Category.assoc, WidePullback.π_arrow]; exact c.condition))
      (fun _ ↦ H.lift_snd _ _ _)
  · intro c
    apply WidePullback.hom_ext
    · intro j
      simp only [Category.assoc, Arrow.mapCechNerve_app, WidePullback.lift_π,
        WidePullback.lift_π_assoc, H.lift_fst]
    · simp only [Category.assoc, Arrow.mapCechNerve_app, WidePullback.lift_base,
        WidePullback.lift_base_assoc]
      exact c.condition.symm
  · intro c
    exact WidePullback.lift_base _ _ _ _
  · intro c m hm ht
    apply WidePullback.hom_ext
    · intro j
      rw [WidePullback.lift_π]
      apply H.hom_ext
      · rw [H.lift_fst]
        have hh := congrArg
          (fun k ↦ k ≫ WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ g.hom) j) hm
        simpa only [Category.assoc, Arrow.mapCechNerve_app, WidePullback.lift_π] using hh
      · rw [H.lift_snd, Category.assoc, WidePullback.π_arrow]
        exact ht
    · rw [WidePullback.lift_base]
      exact ht

end SerrePositivity.AlgebraicGeometry
