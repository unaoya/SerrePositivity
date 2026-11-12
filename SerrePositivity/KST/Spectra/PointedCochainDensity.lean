module

public import SerrePositivity.KST.Spectra.CochainDensityCone
public import SerrePositivity.KST.Spectra.PointedWeightedEndBasepoint

/-!
概要：通常の cochain の Tot と完全な重みの end の基点を保つ密度の同型。
方針：各基点からなる厳密な錐の標準射に対する密度の整合式を使う。
規約：点つき単体集合の実際の同型であり Kan 条件は不要。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。hG と Tot の点つき比較。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Opposite


namespace SerrePositivity.KST.Spectra.SimplexDensity

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {I : Type u} [SmallCategory I] (W : I ⥤ SSet.{u})
    (D : I ⥤ PointedSimplicialSet.{u})

lemma basepointFamily_underlyingIso :
    PointedTotalization.basepointFamily (weightedCochains (discreteLevels W) D) ≫
        (UnderlyingWeightedCochains.pointedUnderlyingIso (discreteLevels W) D).hom =
      coneFamily W (PointedWeightedEnd.basepointCone D) := by
  apply NatTrans.ext
  funext n
  change (snd (SSet.stdSimplex.obj n) (𝟙_ SSet.{u}) ≫
      (PointedWeightedEnd.obj ((discreteLevels W).obj (op n)) D).hom) ≫
        (PointedWeightedEnd.underlyingIso ((discreteLevels W).obj (op n)) D).hom = _
  rw [Category.assoc, PointedWeightedEnd.underlyingIso_basepoint]
  rfl

lemma pointedUnderlyingTotalizationEndIso_basepoint :
    (PointedTotalization.obj (weightedCochains (discreteLevels W) D)).hom ≫
        (pointedUnderlyingTotalizationEndIso W D).hom =
      (PointedWeightedEnd.obj W D).hom := by
  change CosimplicialTotalization.lift
      (PointedTotalization.basepointFamily (weightedCochains (discreteLevels W) D)) ≫
      ((CosimplicialTotalization.map
          (UnderlyingWeightedCochains.pointedUnderlyingIso (discreteLevels W) D).hom ≫
        (totalizationEndIso W (D ⋙ PointedSimplicialSet.forget)).hom) ≫
          (PointedWeightedEnd.underlyingIso W D).inv) = _
  rw [← Category.assoc, ← Category.assoc, CosimplicialTotalization.lift_post,
    basepointFamily_underlyingIso, totalizationEndIso_cone,
    ← PointedWeightedEnd.underlyingIso_basepoint, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- 概要：点つき cochain の通常の Tot と点つき end の基点を保つ同型。
方針：基礎の密度の同型と各係数の基点の錐の整合式を使う。
規約：任意の点つき係数と重みの図式について定義する。
使われ方：Goerss–Jardine VIII §§1–2、HA §1.4.2。通常の Tot の点つき end 表示。 -/
def pointedTotalizationEndIso :
    PointedTotalization.obj (weightedCochains (discreteLevels W) D) ≅
      PointedWeightedEnd.obj W D :=
  Under.isoMk (pointedUnderlyingTotalizationEndIso W D)
    (pointedUnderlyingTotalizationEndIso_basepoint W D)

end

end SerrePositivity.KST.Spectra.SimplexDensity
