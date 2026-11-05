module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplicialCategory.Basic

/-!
概要：単体的豊穣圏のパラメータ付き円柱の Hom と合成。
方針：同じ端の Hom は元の Hom、左から右へはパラメータとの積、逆方向は空とする。
規約：端をまたぐ射は一度だけ合成できる。使われ方：普遍評価の coherent な族。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
namespace SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder
open SerrePositivity.KST.Spectra.EnrichedParameterCylinder

/-- 各単体が空である単体集合。 -/
def empty : SSet.{u} := (Functor.const SimplexCategoryᵒᵖ).obj PEmpty.{u + 1}

/-- 空な第一因子からの射。 -/
def emptyLeft (X Y : SSet.{u}) : empty ⊗ X ⟶ Y where
  app _ := ↾fun x ↦ PEmpty.elim x.1
  naturality {d e} f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨e, x⟩
    exact e.elim

/-- 空な第二因子からの射。 -/
def emptyRight (X Y : SSet.{u}) : X ⊗ empty ⟶ Y where
  app _ := ↾fun x ↦ PEmpty.elim x.2
  naturality {d e} f := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, e⟩
    exact e.elim

/-- 端の組に応じた、元の Hom とパラメータ付き Hom。 -/
def homBySide (A : SSet.{u}) : Bool → Bool → SSet.{u} → SSet.{u}
  | false, false, H => H
  | false, true, H => A ⊗ H
  | true, false, _ => empty
  | true, true, H => H

/-- 同じ端の恒等射。 -/
def identityBySide (A H : SSet.{u}) (i : 𝟙_ SSet.{u} ⟶ H) :
    (s : Bool) → 𝟙_ SSet.{u} ⟶ homBySide A s s H
  | false => i
  | true => i

/-- 元の合成を、パラメータを一つだけ保持して延長する。 -/
def compositionBySide (A : SSet.{u}) {H K L : SSet.{u}} (m : H ⊗ K ⟶ L) :
    (s t r : Bool) → homBySide A s t H ⊗ homBySide A t r K ⟶ homBySide A s r L
  | false, false, false => m
  | false, false, true =>
      lift (snd H (A ⊗ K) ≫ fst A K) ((𝟙 H ⊗ₘ snd A K) ≫ m)
  | false, true, false => emptyRight _ _
  | false, true, true =>
      lift (fst (A ⊗ H) K ≫ fst A H) ((snd A H ⊗ₘ 𝟙 K) ≫ m)
  | true, false, false => emptyLeft _ _
  | true, false, true => emptyLeft _ _
  | true, true, false => emptyRight _ _
  | true, true, true => m

/-- 円柱の対象は端と元の対象の組。 -/
structure Object (A : SSet.{u}) (C : Type v) where
  /-- false が左端、true が右端。 -/
  side : Bool
  /-- 元の豊穣圏の対象。 -/
  val : C

variable (A : SSet.{u}) {C : Type v} [EnrichedCategory SSet.{u} C]

/-- 円柱の実際の豊穣 Hom。 -/
def hom (X Y : Object A C) : SSet.{u} := homBySide A X.side Y.side (X.val ⟶[SSet] Y.val)

/-- 円柱の実際の恒等射。 -/
def identity (X : Object A C) : 𝟙_ SSet.{u} ⟶ hom A X X :=
  identityBySide A (X.val ⟶[SSet] X.val) (eId SSet X.val) X.side

/-- 円柱の実際の合成。 -/
def composition (X Y Z : Object A C) : hom A X Y ⊗ hom A Y Z ⟶ hom A X Z :=
  compositionBySide A (eComp SSet X.val Y.val Z.val) X.side Y.side Z.side

end SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.composition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.composition := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.composition

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.compositionBySide (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.compositionBySide := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.compositionBySide

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.empty (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.empty := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.empty

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.emptyLeft (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.emptyLeft := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.emptyLeft

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.emptyRight (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.emptyRight := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.emptyRight

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.hom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.hom := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.hom

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.homBySide (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.homBySide := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.homBySide

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.identity (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.identity := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.identity

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.identityBySide (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.identityBySide := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.identityBySide

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.casesOn := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.ctorIdx := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.mk := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.noConfusionType := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.rec := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.recOn := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.side (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.side := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.side

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.val (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.val := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.val

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.compositionBySide.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.compositionBySide.match_1 := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.compositionBySide.match_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.emptyLeft._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.emptyLeft._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.emptyRight._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.emptyRight._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.homBySide.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.homBySide.match_1 := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.homBySide.match_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.identityBySide.match_1 (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.identityBySide.match_1 := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.identityBySide.match_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.mk.inj := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.mk.injEq := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.Object.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Kan.EnrichedParameterCylinder.Object.mk.sizeOf_spec
