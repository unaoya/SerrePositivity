module

public import SerrePositivity.KST.Spectra.OrdinaryLoopUniversalInterval
public import SerrePositivity.KST.Spectra.PointedIntervalConjugateSquare
public import SerrePositivity.KST.Spectra.TripleCircleLoopExchangeBoundary
public import SerrePositivity.KST.Spectra.LoopExchangeFamily

/-!
概要：通常 loop 値の普遍交換区間に、同じ左右境界を固定する実自然性正方形を与える。
方針：混合源の同じ自然性正方形を curry 座標へ移し、全境界の厳密な頂点を計算する。
規約：辺・正方形の再選択なし。使われ方：元の通常円随伴の厳密自然性への接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OrdinaryLoopSource

variable {Z Z' : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex Z'.right]
  (v : Z ⟶ Z')

/-- 同じ混合源の全写像族の正方形を、同じ curry 座標へ写した二次元射。 -/
def loopExchangeNaturalityData :=
  PointedMapping.conjugateSquare (sourceInterval Z) (sourceInterval Z')
    (PointedObject.basedHomMap source.{u} v)
    (UniversalSourceInterval.naturalitySquare specification.{u} v)
    (mappingIso Z) (mappingIso Z') (loopPost v)
    (TwoLoopSource.mappingIso_post PointedSimplicialSet.circle.{u} v).symm

/-- 元の通常 loop 値の普遍交換区間の、同じ両端境界を固定する自然性正方形。 -/
def loopExchangeNaturalitySquare :
    SSet.Homotopy (((loopExchangeInterval Z).basedPost (loopPost v)).path)
      (((loopExchangeInterval Z').pre (loopPost v)).path) where
  h := (loopExchangeNaturalityData v).h
  h₀ := by
    change SSet.ι₀ ≫ (loopExchangeNaturalityData v).h =
      (loopExchangeInterval Z).path ≫
        (PointedObject.basedHomMap
          (LoopExchangePaths.doubleLoop
            (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)) (loopPost v)).right
    rw [loopExchangeInterval_path]
    exact (loopExchangeNaturalityData v).h₀
  h₁ := by
    change SSet.ι₁ ≫ (loopExchangeNaturalityData v).h =
      (loopExchangeInterval Z').path ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (loopPost v)
          (LoopExchangePaths.doubleLoop
            (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z'))).right
    rw [loopExchangeInterval_path]
    exact (loopExchangeNaturalityData v).h₁
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

omit [KanComplex Z.right] [KanComplex Z'.right] in
/-- 同じ源作用の curry 座標像は、元の通常 loop の後合成と作用の厳密な合成。 -/
lemma mappingIso_conjugate_pre (a : source.{u} ⟶ source.{u})
    (t : LoopExchangePaths.doubleLoop (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z') ⟶
      LoopExchangePaths.doubleLoop (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z'))
    (ht : _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z' ≫ (mappingIso Z').hom = (mappingIso Z').hom ≫ t) :
    (mappingIso Z).inv ≫
        ((PointedObject.basedHomMap source.{u} v ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z') ≫
          (mappingIso Z').hom) = loopPost v ≫ t := by
  simp only [Category.assoc]
  rw [ht, ← Category.assoc (PointedObject.basedHomMap source.{u} v),
    TwoLoopSource.mappingIso_post]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- 左辺全体は、通常 loop の後合成と元の交換作用の同じ頂点で一定。 -/
lemma loopExchangeNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (loopExchangeNaturalitySquare v).h =
      SSet.const (PointedMapping.familyVertex (loopPost v ≫
        LoopExchangePaths.swap (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z'))) := by
  change SquareAdjustment.leftSide ≫
    ((UniversalSourceInterval.naturalitySquare specification.{u} v).h ≫
      (PointedMapping.coordinateMap (mappingIso Z).inv (mappingIso Z').hom).right) = _
  rw [← Category.assoc, UniversalSourceInterval.naturalitySquare_start,
    SSet.const_comp]
  have hv := PointedMapping.coordinateMap_vertex (mappingIso Z).inv (mappingIso Z').hom
    (PointedObject.basedHomMap source.{u} v ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed swap.{u} Z')
  have he := mappingIso_conjugate_pre v swap.{u} _
    (TwoLoopSource.mappingIso_pre_swap PointedSimplicialSet.circle.{u} Z')
  exact (congrArg (fun x => SSet.const (X := (Δ[1] : SSet.{u})) x) hv).trans
    (congrArg (fun f => SSet.const (PointedMapping.familyVertex f)) he)

/-- 右辺全体も、通常 loop の後合成と元の反転作用の同じ頂点で一定。 -/
lemma loopExchangeNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (loopExchangeNaturalitySquare v).h =
      SSet.const (PointedMapping.familyVertex (loopPost v ≫
        LoopExchangePaths.reversal
          (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z'))) := by
  change SquareAdjustment.rightSide ≫
    ((UniversalSourceInterval.naturalitySquare specification.{u} v).h ≫
      (PointedMapping.coordinateMap (mappingIso Z).inv (mappingIso Z').hom).right) = _
  rw [← Category.assoc, UniversalSourceInterval.naturalitySquare_finish,
    SSet.const_comp]
  have hv := PointedMapping.coordinateMap_vertex (mappingIso Z).inv (mappingIso Z').hom
    (PointedObject.basedHomMap source.{u} v ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed reversal.{u} Z')
  have he := mappingIso_conjugate_pre v reversal.{u} _
    (TwoLoopSource.mappingIso_pre_reversal PointedSimplicialSet.circle.{u} Z')
  exact (congrArg (fun x => SSet.const (X := (Δ[1] : SSet.{u})) x) hv).trans
    (congrArg (fun f => SSet.const (PointedMapping.familyVertex f)) he)

/-- 全ての実区間・自然性正方形・左右全境界を供給した、通常円の交換族。 -/
def family : LoopExchangeFamily PointedSimplicialSet.circle.{u} where
  interval := loopExchangeInterval
  naturality := loopExchangeNaturalitySquare
  start := loopExchangeNaturalitySquare_start
  finish := loopExchangeNaturalitySquare_finish

end SerrePositivity.KST.Spectra.OrdinaryLoopSource
