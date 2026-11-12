module

public import SerrePositivity.KST.Spectra.TripleCircleLoopExchangeNaturality

/-!
概要：三重 loop の自然性正方形の一定境界を、元の loop 作用の同じ頂点で表示する。
方針：curry 座標の前後合成を頂点へ作用させ、厳密な自然性で相殺する。
規約：境界全体の等式。使われ方：Ω 対象の交換トレースとの共通境界。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra

/-- 同じ前後合成の座標射は、元の族の頂点をその厳密な前後合成へ送る。 -/
lemma PointedMapping.coordinateMap_vertex {A A' B B' : PointedSimplicialSet.{u}}
    (i : A' ⟶ A) (j : B ⟶ B') (f : A ⟶ B) :
    (PointedMapping.coordinateMap i j).right.app _ (PointedMapping.familyVertex f) =
      PointedMapping.familyVertex (i ≫ (f ≫ j)) := by
  change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i B').right.app _
    ((PointedObject.basedHomMap A j).right.app _ (PointedMapping.familyVertex f)) = _
  rw [PointedMapping.familyVertex_post]
  exact PointedMapping.familyVertex_pre i (f ≫ j)

namespace TripleCircle

private lemma conjugate_pre {Z Z' : PointedSimplicialSet.{u}} (v : Z ⟶ Z')
    (a : source.{u} ⟶ source.{u})
    (t : LoopExchangePaths.doubleLoop (PointedObject.basedHom CirclePower.space.{u} Z') ⟶
      LoopExchangePaths.doubleLoop (PointedObject.basedHom CirclePower.space.{u} Z'))
    (ht : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z' ≫ (mappingIso Z').hom = (mappingIso Z').hom ≫ t) :
    (mappingIso Z).inv ≫
        ((PointedObject.basedHomMap source.{u} v ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z') ≫
          (mappingIso Z').hom) = loopPost v ≫ t := by
  simp only [Category.assoc]
  rw [ht, ← Category.assoc (PointedObject.basedHomMap source.{u} v), mappingIso_post]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

variable {Z Z' : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex Z'.right]
  (v : Z ⟶ Z')

/-- 左辺全体は、元の三重 loop 後合成と交換作用の同じ合成頂点。 -/
lemma loopExchangeNaturalitySquare_start_vertex :
    SquareAdjustment.leftSide ≫ (loopExchangeNaturalitySquare v).h =
      SSet.const (PointedMapping.familyVertex (loopPost v ≫
        LoopExchangePaths.swap (PointedObject.basedHom CirclePower.space.{u} Z'))) := by
  rw [loopExchangeNaturalitySquare_start, SSet.const_comp, PointedMapping.coordinateMap_vertex]
  rw [conjugate_pre v swap.{u} _ (mappingIso_pre_swap Z')]

/-- 右辺全体も、元の三重 loop 後合成と反転作用の同じ合成頂点。 -/
lemma loopExchangeNaturalitySquare_finish_vertex :
    SquareAdjustment.rightSide ≫ (loopExchangeNaturalitySquare v).h =
      SSet.const (PointedMapping.familyVertex (loopPost v ≫
        LoopExchangePaths.reversal (PointedObject.basedHom CirclePower.space.{u} Z'))) := by
  rw [loopExchangeNaturalitySquare_finish, SSet.const_comp, PointedMapping.coordinateMap_vertex]
  rw [conjugate_pre v reversal.{u} _ (mappingIso_pre_reversal Z')]

end TripleCircle
end SerrePositivity.KST.Spectra
