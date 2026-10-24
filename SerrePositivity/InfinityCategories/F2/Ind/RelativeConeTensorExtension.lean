module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCoconeNaturality
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeTerminalCocone

/-!
概要：元の補間余錐を、部分形状の全拡張を固定したまま元の余錐の積へ戻す。
方針：終対象への相対余錐延長と、元の全形状同型の厳密な自然性を合成する。
規約：部分形状上の元の全円柱と、補間領域の全図式を同時に保持する。
使われ方：点追加で元の旧族と指定 D を固定した全図式を再構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 概要：指定した部分形状の全円柱を変えず、補間領域の元の全図式を拡張できる。
方針：終対象への相対延長。規約：元の全射の等号。使われ方：旧族の厳密な回収。 -/
lemma exists_relative_coneTensor_extension {A B L X : SSet.{u}} (f : A ⟶ B) [Mono f]
    (H : coneTensorCorner B L ⟶ X) (t : X _⦋0⦌) (ht : IsTerminalVertex t)
    (c : JoinCocone (coneTensorCornerMap f L ≫ H)) (hc : c.vertex = t) :
    ∃ R : join B (Δ[0] : SSet.{u}) ⊗ join L Δ[0] ⟶ X,
      coneTensorCornerInclusion B L ≫ R = H ∧
      (joinMap f (𝟙 Δ[0]) ▷ join L (Δ[0] : SSet.{u})) ≫ R =
        (coneTensorCoconeIso A L).inv ≫ c.val := by
  obtain ⟨d, _, hd⟩ := exists_relative_terminal_cocone (coneTensorCornerMap f L) H t ht c hc
  let R := (coneTensorCoconeIso B L).inv ≫ d.val
  have hi : coneTensorCornerInclusion B L ≫ (coneTensorCoconeIso B L).inv =
      joinInl (coneTensorCorner B L) (Δ[0] : SSet.{u}) := by
    apply (cancel_mono (coneTensorCoconeIso B L).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (coneTensorCocone_inl B L).symm
  refine ⟨R, ?_, ?_⟩
  · change coneTensorCornerInclusion B L ≫ (coneTensorCoconeIso B L).inv ≫ d.val = H
    rw [← Category.assoc, hi]
    exact d.property
  · change (joinMap f (𝟙 Δ[0]) ▷ join L (Δ[0] : SSet.{u})) ≫
      (coneTensorCoconeIso B L).inv ≫ d.val = _
    rw [← Category.assoc, coneTensorCoconeIso_inv_naturality, Category.assoc, hd]

/-- 概要：元の全円柱と補間領域の全図式を同時に保持する再構成。
方針：元の円柱を相対余錐として渡す。規約：全射の等号。使われ方：旧族の厳密な回収。 -/
lemma exists_coneTensor_extension_fixing_original {A B L X : SSet.{u}}
    (f : A ⟶ B) [Mono f] (H : coneTensorCorner B L ⟶ X)
    (W : join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0] ⟶ X)
    (hW : coneTensorCornerMap f L ≫ H = coneTensorCornerInclusion A L ≫ W)
    (ht : IsTerminalVertex (SSet.yonedaEquiv
      (lift (joinInr A (Δ[0] : SSet.{u})) (joinInr L Δ[0]) ≫ W))) :
    ∃ R : join B (Δ[0] : SSet.{u}) ⊗ join L Δ[0] ⟶ X,
      coneTensorCornerInclusion B L ≫ R = H ∧
      (joinMap f (𝟙 Δ[0]) ▷ join L (Δ[0] : SSet.{u})) ≫ R = W := by
  let c : JoinCocone (coneTensorCornerMap f L ≫ H) :=
    ⟨coneTensorCocone A L ≫ W, by rw [← Category.assoc, coneTensorCocone_inl]; exact hW.symm⟩
  have hc : c.vertex = SSet.yonedaEquiv
      (lift (joinInr A (Δ[0] : SSet.{u})) (joinInr L Δ[0]) ≫ W) := by
    change SSet.yonedaEquiv (joinInr _ _ ≫ (coneTensorCocone A L ≫ W)) = _
    rw [← Category.assoc, coneTensorCocone_inr]
  obtain ⟨R, hR, hOld⟩ := exists_relative_coneTensor_extension f H c.vertex (hc.symm ▸ ht) c rfl
  refine ⟨R, hR, hOld.trans ?_⟩
  change (coneTensorCoconeIso A L).inv ≫ (coneTensorCoconeIso A L).hom ≫ W = W
  rw [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2.Ind
