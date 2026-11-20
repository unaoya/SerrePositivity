module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterSquares

/-!
概要：パラメータ付きの豊穣射の単位律。
方針：豊穣単位律を単位子の自然性と合成する。
規約：任意の豊穣圏。使われ方：cotensor の整合写像空間の恒等射。
-/

@[expose] public section
universe u v w
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra
variable (V : Type u) [Category.{v} V] [MonoidalCategory V]
  {C : Type w} [EnrichedCategory V C]

/-- パラメータ付きの射を恒等射へ後合成すると右単位子で計算される。 -/
lemma enriched_parameter_comp_id {A : V} {X Y : C} (e : A ⟶ (X ⟶[V] Y)) :
    (e ⊗ₘ eId V Y) ≫ eComp V X Y Y = (ρ_ A).hom ≫ e := by
  have hu : (X ⟶[V] Y) ◁ eId V Y ≫ eComp V X Y Y = (ρ_ (X ⟶[V] Y)).hom := by
    apply (cancel_epi (ρ_ (X ⟶[V] Y)).inv).mp
    rw [e_comp_id, Iso.inv_hom_id]
  rw [tensorHom_def, Category.assoc, hu, rightUnitor_naturality]

/-- 恒等射にパラメータ付きの射を後合成すると左単位子で計算される。 -/
lemma enriched_parameter_id_comp {A : V} {X Y : C} (e : A ⟶ (X ⟶[V] Y)) :
    (eId V X ⊗ₘ e) ≫ eComp V X X Y = (λ_ A).hom ≫ e := by
  have hu : eId V X ▷ (X ⟶[V] Y) ≫ eComp V X X Y = (λ_ (X ⟶[V] Y)).hom := by
    apply (cancel_epi (λ_ (X ⟶[V] Y)).inv).mp
    rw [e_id_comp, Iso.inv_hom_id]
  rw [tensorHom_def', Category.assoc, hu, leftUnitor_naturality]

variable [BraidedCategory V]
/-- 両端の恒等射は、任意のパラメータ付き評価と可換。 -/
lemma enriched_parameter_square_id {A : V} {X Y : C} (e : A ⟶ (X ⟶[V] Y)) :
    (e ⊗ₘ eId V Y) ≫ eComp V X Y Y =
      (β_ A (𝟙_ V)).hom ≫ (eId V X ⊗ₘ e) ≫ eComp V X X Y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_comp_id, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_parameter_id_comp,
    ← Category.assoc, braiding_leftUnitor]

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
