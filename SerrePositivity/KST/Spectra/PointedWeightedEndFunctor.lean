module

public import SerrePositivity.KST.Spectra.PointedWeightedConeCompatibility

/-!
概要：点つき weighted end の関手法則と内部 Hom 交換の係数自然性。
方針：全ての式を end の各射影へ戻して内部 Hom の関手法則を使う。
規約：通常の点つき射の厳密な法則。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の Kan 列の射への作用。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.PointedWeightedEnd

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance weightedEndFunctorPointedSelfEnrichment :
    EnrichedOrdinaryCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedOrdinaryCategorySelf PointedSimplicialSet.{u}

variable {I : Type u} [SmallCategory I]

/-- 概要：点つき end は恒等自然変換を恒等射へ送る。
方針：各射影で内部 Hom の恒等法則を使う。
規約：厳密な射の等式。
使われ方：HA §1.4.2。hG・Tot の関手法則。 -/
theorem map_id (W : I ⥤ SSet.{u}) (D : I ⥤ PointedSimplicialSet.{u}) :
    map W (𝟙 D) = 𝟙 (obj W D) := by
  apply end_.hom_ext
  intro i
  rw [map_π, Category.id_comp]
  change end_.π (diagram W D) i ≫ (ihom (PointedObject.adjoin (W.obj i))).map (𝟙 (D.obj i)) = _
  rw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

/-- 概要：点つき end は係数自然変換の合成を保つ。
方針：各射影で内部 Hom の合成保存を使う。
規約：厳密な射の等式。
使われ方：HA §1.4.2、BF 1978 §2。Kan 列の homotopy end の関手性。 -/
theorem map_comp (W : I ⥤ SSet.{u}) {D E F : I ⥤ PointedSimplicialSet.{u}}
    (τ : D ⟶ E) (υ : E ⟶ F) : map W (τ ≫ υ) = map W τ ≫ map W υ := by
  apply end_.hom_ext
  intro i
  rw [map_π, Category.assoc, map_π, ← Category.assoc, map_π,
    Category.assoc, ← CategoryTheory.Functor.map_comp]
  rfl

/-- 概要：固定した重みの点つき end の通常の関手。
方針：実際の射と二つの関手法則を束ねる。
規約：∞ 極限関手の主張は含まない。
使われ方：HA §1.4.2、BF 1978 §2。hG・Tot の各段の関手性。 -/
def functor (W : I ⥤ SSet.{u}) : (I ⥤ PointedSimplicialSet.{u}) ⥤ PointedSimplicialSet.{u} where
  obj := obj W
  map := map W
  map_id := map_id W
  map_comp := map_comp W

/-- 概要：内部 Hom と end の交換は係数自然変換に関して自然。
方針：各射影で内部 Hom の関手法則と二つの源の交換の標的自然性を使う。
規約：重みと内部 Hom の源は固定する。
使われ方：HA §1.4.2、BF 1978 §2。Kan 列の構造射と射への作用の整合性。 -/
@[reassoc]
theorem cotensorIso_natural (A : PointedSimplicialSet.{u}) (W : I ⥤ SSet.{u})
    {D E : I ⥤ PointedSimplicialSet.{u}} (τ : D ⟶ E) :
    (ihom A).map (map W τ) ≫ (cotensorIso A W E).hom =
      (cotensorIso A W D).hom ≫ map W (Functor.whiskerRight τ (ihom A)) := by
  apply end_.hom_ext
  intro i
  rw [Category.assoc, cotensorIso_π, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
    map_π, CategoryTheory.Functor.map_comp, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget.natural_post]
  conv_rhs => rw [Category.assoc, map_π, ← Category.assoc, cotensorIso_π]
  simp only [Category.assoc]
  rfl

end

end SerrePositivity.KST.Spectra.PointedWeightedEnd
