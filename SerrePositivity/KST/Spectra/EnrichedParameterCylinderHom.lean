module

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

end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
