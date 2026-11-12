module

public import SerrePositivity.KST.Spectra.TripleCircleExchangeNaturality
public import SerrePositivity.KST.Spectra.TripleCircleLoopExchange
public import SerrePositivity.KST.Spectra.PointedIntervalCoordinateNaturality

/-!
概要：同じ普遍交換区間の自然性正方形を三重 loop の座標へ移す。
方針：curry 同型の前後合成を、元の正方形の同じ二次元射へ作用させる。
規約：辺や充填を再選択しない。使われ方：Ω 対象へのトレース付き移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.TripleCircle

variable {Z Z' : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex Z'.right]
  (v : Z ⟶ Z')

omit [KanComplex Z.right] [KanComplex Z'.right] in
/-- 逆 curry 座標も、同じ標的後合成と厳密に可換。 -/
lemma mappingIso_inv_post :
    loopPost v ≫ (mappingIso Z').inv =
      (mappingIso Z).inv ≫ PointedObject.basedHomMap source.{u} v := by
  apply (cancel_mono (mappingIso Z').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [mappingIso_post, Iso.inv_hom_id_assoc]

omit [KanComplex Z'.right] in
/-- 始辺の座標像は、元の三重 loop 交換区間の後合成と同じ実辺。 -/
lemma loopExchangeNaturality_zero :
    ((loopExchangeInterval Z).basedPost (loopPost v)).path =
      ((exchangeInterval Z).basedPost (PointedObject.basedHomMap source.{u} v)).path ≫
        (PointedMapping.coordinateMap (mappingIso Z).inv (mappingIso Z').hom).right := by
  change (loopExchangeInterval Z).path ≫ _ = _
  rw [loopExchangeInterval_path]
  exact (exchangeInterval Z).coordinate_post_path (mappingIso Z) (mappingIso Z')
    (PointedObject.basedHomMap source.{u} v) (loopPost v) (mappingIso_post v).symm

/-- 終辺の座標像も、元の三重 loop 交換区間の前合成と同じ実辺。 -/
lemma loopExchangeNaturality_one :
    ((loopExchangeInterval Z').pre (loopPost v)).path =
      ((exchangeInterval Z').pre (PointedObject.basedHomMap source.{u} v)).path ≫
        (PointedMapping.coordinateMap (mappingIso Z).inv (mappingIso Z').hom).right := by
  change (loopExchangeInterval Z').path ≫ _ = _
  rw [loopExchangeInterval_path]
  exact (exchangeInterval Z').coordinate_pre_path (mappingIso Z) (mappingIso Z')
    (PointedObject.basedHomMap source.{u} v) (loopPost v) (mappingIso_inv_post v)

/-- 同じ二次元射の curry 座標像から得る、三重 loop の自然性正方形。 -/
def loopExchangeNaturalitySquare :
    SSet.Homotopy (((loopExchangeInterval Z).basedPost (loopPost v)).path)
      (((loopExchangeInterval Z').pre (loopPost v)).path) where
  h := (exchangeNaturalitySquare v).h ≫
    (PointedMapping.coordinateMap (mappingIso Z).inv (mappingIso Z').hom).right
  h₀ := by
    rw [← Category.assoc, (exchangeNaturalitySquare v).h₀]
    exact (loopExchangeNaturality_zero v).symm
  h₁ := by
    rw [← Category.assoc, (exchangeNaturalitySquare v).h₁]
    exact (loopExchangeNaturality_one v).symm
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 左辺全体は、元の一定な交換境界の同じ座標像。 -/
lemma loopExchangeNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (loopExchangeNaturalitySquare v).h =
      SSet.const (PointedMapping.familyVertex (PointedObject.basedHomMap source.{u} v ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed swap.{u} Z')) ≫
          (PointedMapping.coordinateMap (mappingIso Z).inv (mappingIso Z').hom).right := by
  change SquareAdjustment.leftSide ≫ ((exchangeNaturalitySquare v).h ≫ _) = _
  rw [← Category.assoc, exchangeNaturalitySquare_start]

/-- 右辺全体も、元の一定な反転境界の同じ座標像。 -/
lemma loopExchangeNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (loopExchangeNaturalitySquare v).h =
      SSet.const (PointedMapping.familyVertex (PointedObject.basedHomMap source.{u} v ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed reversal.{u} Z')) ≫
          (PointedMapping.coordinateMap (mappingIso Z).inv (mappingIso Z').hom).right := by
  change SquareAdjustment.rightSide ≫ ((exchangeNaturalitySquare v).h ≫ _) = _
  rw [← Category.assoc, exchangeNaturalitySquare_finish]

end SerrePositivity.KST.Spectra.TripleCircle
