module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinderPairFunctor
public import SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinderRestriction

/-!
概要：円柱の pairing とパラメータ制限の両立。
方針：端ごとの Hom の変更を明示し、同じパラメータを両側で計算する。
規約：対象・元の Hom の族は変えない。使われ方：評価の族の基点への制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
namespace SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder
open SerrePositivity.KST.Spectra.EnrichedParameterCylinder
variable {A B : SSet.{u}} (i : A ⟶ B)

/-- 端ごとの Hom でパラメータだけを変える射。 -/
def changeBySide : (s t : Bool) → (H : SSet.{u}) → _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.homBySide A s t H ⟶ _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.homBySide B s t H
  | false, false, _ => 𝟙 _
  | false, true, _ => i ⊗ₘ 𝟙 _
  | true, false, _ => 𝟙 _
  | true, true, _ => 𝟙 _

/-- 元の円柱の制限射は端ごとの変更で計算される。 -/
lemma restrictionMap_eq_change {C : Type v} [EnrichedCategory SSet.{u} C] (X Y : _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object A C) :
    _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.restrictionMap i X Y = _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.changeBySide i X.side Y.side (X.val ⟶[SSet] Y.val) := by
  rcases X with ⟨s, x⟩
  rcases Y with ⟨t, y⟩
  cases s <;> cases t <;> rfl

/-- Hom の pairing はパラメータ変更と厳密に可換。 -/
lemma pairBySide_change (s t : Bool) {U H : SSet.{u}}
    (k : U ⟶ _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.homBySide A s t (𝟙_ SSet.{u})) (f : U ⟶ H) :
    _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairBySide B s t (k ≫ _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.changeBySide i s t (𝟙_ SSet.{u})) f =
      _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairBySide A s t k f ≫ _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.changeBySide i s t H := by
  cases s <;> cases t
  all_goals
    apply SSet.hom_ext
    intro d
    rfl

/-- 二つの豊穣図式の pairing は、二対象の円柱のパラメータ制限と可換。 -/
lemma pairFunctor_restriction {C : Type v} {T : Type w}
    [EnrichedCategory SSet.{u} C] [EnrichedCategory SSet.{u} T]
    (F : EnrichedFunctor SSet.{u} T C)
    (G : EnrichedFunctor SSet.{u} T (_root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object A _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Point.{v})) :
    _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairFunctor B F (G.comp SSet (_root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.restriction (C := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Point.{v}) i)) =
      (_root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairFunctor A F G).comp SSet (_root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.restriction (C := C) i) := by
  apply EnrichedFunctor.ext SSet
    (F := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairFunctor B F (G.comp SSet (_root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.restriction (C := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Point.{v}) i)))
    (G := (_root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairFunctor A F G).comp SSet (_root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.restriction (C := C) i)) (fun _ ↦ rfl)
  intro X Y
  change _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairBySide B (G.obj X).side (G.obj Y).side
      (G.map X Y ≫ _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.restrictionMap i (G.obj X) (G.obj Y)) (F.map X Y) ≫ 𝟙 _ =
    _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairBySide A (G.obj X).side (G.obj Y).side (G.map X Y) (F.map X Y) ≫
      _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.restrictionMap i (_root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairObject A F G X) (_root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairObject A F G Y)
  rw [Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.restrictionMap_eq_change, _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.restrictionMap_eq_change]
  exact _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairBySide_change i (G.obj X).side (G.obj Y).side (G.map X Y) (F.map X Y)

end SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.changeBySide (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.changeBySide := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.changeBySide

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairBySide_change := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairBySide_change

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.pairFunctor_restriction := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.pairFunctor_restriction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.restrictionMap_eq_change := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.restrictionMap_eq_change

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.changeBySide.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.changeBySide.match_1 := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.changeBySide.match_1
