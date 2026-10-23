module

public import SerrePositivity.InfinityCategories.F1.Diagrams.StrictDiagramMappingSpace

/-!
概要：一点の通常圏上の strict な変換空間は、その同じ対象での内部 Hom と厳密に同型。
方針：各次数で成分評価の単射性と全射性を直接証明する。
規約：図式の値の充填性を仮定しない。
使われ方：零次元セル上の元の分類 Hom 作用の同値性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 一点かつ全射が一意な底では、元の strict 変換の成分評価は厳密な同型。 -/
lemma strictDiagramMappingComponent_isIso_of_subsingleton
    {C : Type u} [Category.{u} C] [Subsingleton C] [Quiver.IsThin C]
    (F G : C ⥤ SSet.{u}) (c : C) : IsIso (strictDiagramMappingComponent F G c) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro n
  rw [isIso_iff_bijective]
  constructor
  · intro η θ h
    apply Subtype.ext
    funext d
    obtain rfl : c = d := Subsingleton.elim _ _
    exact h
  · intro θ
    refine ⟨⟨fun d ↦ (Subsingleton.elim c d) ▸ θ, ?_⟩, ?_⟩
    · intro d e f k α x
      obtain rfl : c = d := Subsingleton.elim _ _
      obtain rfl : c = e := Subsingleton.elim _ _
      obtain rfl : f = 𝟙 c := Subsingleton.elim _ _
      change (G.map (𝟙 c)).app k (θ.app k α x) = θ.app k α ((F.map (𝟙 c)).app k x)
      rw [F.map_id, G.map_id]
      rfl
    · rfl

end SerrePositivity.InfinityCategories
