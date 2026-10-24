module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeConeTensorExtension

/-!
概要：補間の旧族側と下方側を貼り、元の全円柱も同時に固定する。
方針：二境界を元の pushout で貼り、終対象への相対再構成を適用する。
規約：三つの指定全写像を厳密に保持する。
使われ方：scalar comma で得た補間を元の diagram comma の全円柱へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：互換な両全境界と元の全円柱には、それら三者を固定する全拡張が存在。
方針：pushout と終対象への相対延長。規約：全射の等号。使われ方：元の族の再構成。 -/
lemma exists_coneTensor_threeBoundary_extension {A B L X : SSet.{u}}
    (f : A ⟶ B) [Mono f]
    (F : B ⊗ join L (Δ[0] : SSet.{u}) ⟶ X)
    (U : join B (Δ[0] : SSet.{u}) ⊗ L ⟶ X)
    (W : join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0] ⟶ X)
    (h : (B ◁ joinInl L (Δ[0] : SSet.{u})) ≫ F =
      (joinInl B (Δ[0] : SSet.{u}) ▷ L) ≫ U)
    (hF : (f ▷ join L (Δ[0] : SSet.{u})) ≫ F =
      (joinInl A (Δ[0] : SSet.{u}) ▷ join L Δ[0]) ≫ W)
    (hU : (joinMap f (𝟙 (Δ[0] : SSet.{u})) ▷ L) ≫ U =
      (join A (Δ[0] : SSet.{u}) ◁ joinInl L Δ[0]) ≫ W)
    (ht : IsTerminalVertex (SSet.yonedaEquiv
      (lift (joinInr A (Δ[0] : SSet.{u})) (joinInr L Δ[0]) ≫ W))) :
    ∃ R : join B (Δ[0] : SSet.{u}) ⊗ join L Δ[0] ⟶ X,
      (joinInl B (Δ[0] : SSet.{u}) ▷ join L Δ[0]) ≫ R = F ∧
      (join B (Δ[0] : SSet.{u}) ◁ joinInl L Δ[0]) ≫ R = U ∧
      (joinMap f (𝟙 (Δ[0] : SSet.{u})) ▷ join L Δ[0]) ≫ R = W := by
  let H : coneTensorCorner B L ⟶ X := pushout.desc F U h
  have hOld : coneTensorCornerMap f L ≫ H = coneTensorCornerInclusion A L ≫ W := by
    apply pushout.hom_ext
    · rw [← Category.assoc, coneTensorCornerMap_old, Category.assoc]
      change (f ▷ join L (Δ[0] : SSet.{u})) ≫
        (pushout.inl _ _ ≫ pushout.desc F U h) = _
      rw [pushout.inl_desc, hF, ← Category.assoc, coneTensorCornerInclusion_old]
    · rw [← Category.assoc, coneTensorCornerMap_lower, Category.assoc]
      change (joinMap f (𝟙 (Δ[0] : SSet.{u})) ▷ L) ≫
        (pushout.inr _ _ ≫ pushout.desc F U h) = _
      rw [pushout.inr_desc, hU, ← Category.assoc, coneTensorCornerInclusion_lower]
  obtain ⟨R, hR, hRW⟩ := exists_coneTensor_extension_fixing_original f H W hOld ht
  refine ⟨R, ?_, ?_, hRW⟩
  · rw [← coneTensorCornerInclusion_old, Category.assoc, hR]
    exact pushout.inl_desc F U h
  · rw [← coneTensorCornerInclusion_lower, Category.assoc, hR]
    exact pushout.inr_desc F U h
end SerrePositivity.InfinityCategories.F2.Ind
