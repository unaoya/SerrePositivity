module

public import SerrePositivity.KST.Spectra.PointedTotalization

/-!
概要：通常の Tot の係数に関する関手性と点つき射への拡張。
方針：標準単体上の普遍的な族を係数の自然変換で後合成する。
規約：任意の余単体図式について通常の圏の関手を与える。
使われ方：Goerss–Jardine VIII §1、HTT A.3.3。Tot の置換比較と自然性。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance totalizationFunctorSelfEnrichment : EnrichedOrdinaryCategory SSet.{u} SSet.{u} :=
  enrichedOrdinaryCategorySelf SSet.{u}

namespace CosimplicialTotalization

/-- 概要：係数の自然変換が誘導する通常の Tot の射。
方針：普遍的な標準単体の族を後合成して end へ戻す。
規約：Reedy 条件や Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。Tot の射への作用。 -/
def map {X Y : CosimplicialObject SSet.{u}} (f : X ⟶ Y) : obj X ⟶ obj Y :=
  lift (uncurry (𝟙 (obj X)) ≫ f)

@[reassoc]
lemma map_π {X Y : CosimplicialObject SSet.{u}} (f : X ⟶ Y) (j : SimplexCategory) :
    map f ≫ π Y j = π X j ≫ (ihom (SSet.stdSimplex.obj j)).map (f.app j) := by
  rw [map, lift_π]
  change curry (MonoidalClosed.uncurry (𝟙 _ ≫ π X j) ≫ f.app j) = _
  rw [curry_natural_right, curry_uncurry, Category.id_comp]

lemma map_id (X : CosimplicialObject SSet.{u}) : map (𝟙 X) = 𝟙 (obj X) := by
  apply end_.hom_ext
  intro j
  change map (𝟙 X) ≫ π X j = 𝟙 _ ≫ π X j
  rw [map_π]
  simp only [NatTrans.id_app, CategoryTheory.Functor.map_id, Category.comp_id,
    Category.id_comp]

lemma map_comp {X Y Z : CosimplicialObject SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = map f ≫ map g := by
  apply end_.hom_ext
  intro j
  change map (f ≫ g) ≫ π Z j = (map f ≫ map g) ≫ π Z j
  rw [map_π, Category.assoc, map_π, ← Category.assoc, map_π,
    NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc]

/-- 概要：通常の Tot を係数の図式に関する関手にする。
方針：実際の射と恒等・合成の法則を束ねる。
規約：∞ 極限の普遍性は主張しない。
使われ方：Goerss–Jardine VIII §1。通常の Tot の自然な比較。 -/
def functor : CosimplicialObject SSet.{u} ⥤ SSet.{u} where
  obj := obj
  map := map
  map_id := map_id
  map_comp := map_comp

end CosimplicialTotalization

namespace PointedTotalization

/-- 概要：点つき係数の自然変換が誘導する通常の点つき Tot の射。
方針：Tot の後合成の射が基点の定数族を保つことを各射影で示す。
規約：元の図式の Reedy 条件は不要。
使われ方：Goerss–Jardine VIII §1。点つき Tot の射への作用。 -/
def map {X Y : CosimplicialObject PointedSimplicialSet.{u}} (f : X ⟶ Y) : obj X ⟶ obj Y :=
  Under.homMk (CosimplicialTotalization.map (Functor.whiskerRight f PointedSimplicialSet.forget))
    (by
      apply end_.hom_ext
      intro j
      change ((CosimplicialTotalization.lift (basepointFamily X) ≫
        CosimplicialTotalization.map (Functor.whiskerRight f PointedSimplicialSet.forget)) ≫
          CosimplicialTotalization.π (Y ⋙ PointedSimplicialSet.forget) j) =
        CosimplicialTotalization.lift (basepointFamily Y) ≫
          CosimplicialTotalization.π (Y ⋙ PointedSimplicialSet.forget) j
      rw [Category.assoc, CosimplicialTotalization.map_π, ← Category.assoc,
        CosimplicialTotalization.lift_π, CosimplicialTotalization.lift_π,
        ← curry_natural_right]
      apply congrArg curry
      change (_ ≫ (X.obj j).hom) ≫ (f.app j).right = _ ≫ (Y.obj j).hom
      rw [Category.assoc, Under.w])

lemma map_id (X : CosimplicialObject PointedSimplicialSet.{u}) : map (𝟙 X) = 𝟙 (obj X) := by
  apply Under.UnderMorphism.ext
  exact CosimplicialTotalization.map_id (X ⋙ PointedSimplicialSet.forget)

lemma map_comp {X Y Z : CosimplicialObject PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) = map f ≫ map g := by
  apply Under.UnderMorphism.ext
  exact CosimplicialTotalization.map_comp
    (Functor.whiskerRight f PointedSimplicialSet.forget)
    (Functor.whiskerRight g PointedSimplicialSet.forget)

/-- 概要：通常の点つき Tot の実際の関手。
方針：基点を保存する射の恒等・合成法則を束ねる。
規約：値の Kan 性は入力の Reedy 条件に依存する。
使われ方：Goerss–Jardine VIII §1、HTT A.3.3。置換した Tot への射。 -/
def functor : CosimplicialObject PointedSimplicialSet.{u} ⥤ PointedSimplicialSet.{u} where
  obj := obj
  map := map
  map_id := map_id
  map_comp := map_comp

end PointedTotalization

end

end SerrePositivity.KST.Spectra
