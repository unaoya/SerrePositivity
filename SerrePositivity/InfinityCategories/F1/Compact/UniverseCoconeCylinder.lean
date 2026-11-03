module

public import SerrePositivity.InfinityCategories.Core.FatJoinComparison
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinCylinderSimplex
public import SerrePositivity.InfinityCategories.Core.JoinTensor
public import SerrePositivity.InfinityCategories.Core.JoinTensorRight
public import SerrePositivity.InfinityCategories.Core.UniverseJoinAugmentation
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexShapes
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.CoconeUnitCylinder
public import SerrePositivity.InfinityCategories.F1.Universe.Prism
public import SerrePositivity.InfinityCategories.PinchedHom.Basic

/-!
概要：元の join 単位円柱の宇宙持ち上げを、持ち上げた余錐の同じ円柱へ照合する。
方針：全単体の元の切断・左右の制限を、余錐形状の厳密な宇宙同型で比較する。
規約：元の標準円柱を同じ射の等式で保持する。
使われ方：同じ底を持つ二つの実 prism の終点の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の prism の係数への前合成は、その同じ射の宇宙持ち上げと可換。 -/
lemma uliftSimplexPrism_precomp {A D E : SSet.{u}} {n : ℕ}
    (H : (Δ[n] : SSet.{u}) ⊗ A ⟶ E) (f : D ⟶ A) :
    uliftSimplexPrism.{u, v} ((Δ[n] ◁ f) ≫ H) =
      (Δ[n] ◁ (SSet.uliftFunctor.{v, u}).map f) ≫ uliftSimplexPrism.{u, v} H := rfl

/-- 同じ元の単位円柱の宇宙持ち上げは、元の余錐の形状同型に厳密に整合する。 -/
lemma uliftCoconeUnitCylinder (B : SSet.{u}) :
    uliftSimplexPrism.{u, v}
      ((β_ (Δ[1] : SSet.{u}) B).hom ≫ coconeUnitCylinderMap B) =
      (β_ (Δ[1] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj B)).hom ≫
        coconeUnitCylinderMap ((SSet.uliftFunctor.{v, u}).obj B) ≫
          (uliftCoconeShapeIso.{u, v} B 0).inv := by
  apply (cancel_mono (uliftCoconeShapeIso.{u, v} B 0).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, x⟩
  change (uliftCoconeShapeIso.{u, v} B 0).hom.app _
    (ULift.up ((joinCylinderMap B Δ[0]).app _
      ((x.down, ULift.up t.down), PinchedHom.constant
        (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))) n))) =
      (joinCylinderMap ((SSet.uliftFunctor.{v, u}).obj B) Δ[0]).app _
        ((x, t), PinchedHom.constant (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{max u v}))) n)
  rw [joinCylinderMap_app, joinCylinderMap_app]
  refine Join.Simplex.ext _ _ rfl ?_ ?_
  · simp only [cast_eq]
    change Join.augHom (𝟙 ((SSet.uliftFunctor.{v, u}).obj B)) _
      (uliftJoinAugUp B _ (Join.augMap B
        (Join.prefixIncl (n + 1)
          ((joinStdSimplexIso.{u} 0 0).inv.app _ (ULift.up t.down)).1.val _) x.down)) = _
    rw [Join.augHom_id]
    exact uliftJoinAugUp_map B
      (Join.prefixIncl (n + 1)
        ((joinStdSimplexIso.{u} 0 0).inv.app _ (ULift.up t.down)).1.val _)
      (show Join.augObj B (n + 1) from x.down)
  · have h (r : ℕ) : Subsingleton (Join.augObj (Δ[0] : SSet.{max u v}) r) := by
      cases r with
      | zero =>
        change Subsingleton PUnit
        infer_instance
      | succ r =>
        change Subsingleton ((Δ[0] : SSet.{max u v}) _⦋r⦌)
        refine ⟨fun a b ↦ ?_⟩
        apply SSet.stdSimplex.ext
        intro i
        apply Fin.ext
        omega
    exact @Subsingleton.elim _ (h _) _ _

end SerrePositivity.InfinityCategories.F2.Compact
