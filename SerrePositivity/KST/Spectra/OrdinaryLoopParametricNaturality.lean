module

public import SerrePositivity.KST.Spectra.OrdinaryLoopParametricCoordinates

/-!
概要：元の通常円の交換区間の全族自然性を、同じ混合源の普遍正方形から回収する。
方針：同じ写像空間同型とそのパラメータ内部 Hom 像で共役し、元の二辺を照合する。
規約：元の区間・両端全境界を保持。使われ方：元の随伴への trace の全族比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OrdinaryLoopSource
variable {P Z Z' : PointedSimplicialSet.{u}} [KanComplex Z.right] [KanComplex Z'.right]
  (v : P ⟶ PointedObject.basedHom Z Z')

/-- 同じ混合源の全族正方形を、元の二重 loop の同じ curry 座標へ移した二次元射。 -/
def loopExchangeParametricNaturalityData :=
  PointedMapping.conjugateSquare (sourceInterval Z) ((sourceInterval Z').basedIhomMap P)
    (PointedMapping.parametricPost source.{u} v)
    (UniversalSourceInterval.parametricNaturalitySquare specification.{u} v)
    (mappingIso Z) (PointedMapping.cotensorIso P (mappingIso Z')) (parametricLoopPost v)
    (mappingIso_parametricPost v)

/-- 現在の通常円交換区間自身の、同じ共役族作用に対する全パラメータ実自然性正方形。 -/
def loopExchangeParametricNaturalitySquare :
    SSet.Homotopy (((loopExchangeInterval Z).basedPost (parametricLoopPost v)).path)
      ((((loopExchangeInterval Z').basedIhomMap P).pre (parametricLoopPost v)).path) where
  h := (loopExchangeParametricNaturalityData v).h
  h₀ := by
    change SSet.ι₀ ≫ (loopExchangeParametricNaturalityData v).h =
      (loopExchangeInterval Z).path ≫ (PointedObject.basedHomMap
        (LoopExchangePaths.doubleLoop (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z))
          (parametricLoopPost v)).right
    rw [loopExchangeInterval_path]
    exact (loopExchangeParametricNaturalityData v).h₀
  h₁ := by
    change SSet.ι₁ ≫ (loopExchangeParametricNaturalityData v).h =
      ((loopExchangeInterval Z').basedIhomMap P).path ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (parametricLoopPost v) (PointedObject.basedHom P
          (LoopExchangePaths.doubleLoop
            (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z')))).right
    rw [loopExchangeInterval_parametricPath]
    exact (loopExchangeParametricNaturalityData v).h₁
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 左境界全体は、共役した同じ全族と元の交換作用の合成頂点で一定。 -/
lemma loopExchangeParametricNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (loopExchangeParametricNaturalitySquare v).h =
      SSet.const (PointedMapping.familyVertex (parametricLoopPost v ≫
        PointedObject.basedHomMap P (LoopExchangePaths.swap
          (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z')))) := by
  change SquareAdjustment.leftSide ≫
    ((UniversalSourceInterval.parametricNaturalitySquare specification.{u} v).h ≫
      (PointedMapping.coordinateMap (mappingIso Z).inv
        (PointedObject.basedHomMap P (mappingIso Z').hom)).right) = _
  rw [← Category.assoc, UniversalSourceInterval.parametricNaturalitySquare_start, SSet.const_comp]
  have hv := PointedMapping.coordinateMap_vertex (mappingIso Z).inv
    (PointedObject.basedHomMap P (mappingIso Z').hom)
    (PointedMapping.parametricPost source.{u} v ≫
      PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed swap.{u} Z'))
  have he := mappingIso_parametric_conjugate_pre v swap.{u} _
    (TwoLoopSource.mappingIso_pre_swap PointedSimplicialSet.circle.{u} Z')
  exact (congrArg (fun x => SSet.const (X := (Δ[1] : SSet.{u})) x) hv).trans
    (congrArg (fun f => SSet.const (PointedMapping.familyVertex f)) he)

/-- 右境界全体も、共役した同じ全族と元の反転作用の合成頂点で一定。 -/
lemma loopExchangeParametricNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (loopExchangeParametricNaturalitySquare v).h =
      SSet.const (PointedMapping.familyVertex (parametricLoopPost v ≫
        PointedObject.basedHomMap P (LoopExchangePaths.reversal
          (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z')))) := by
  change SquareAdjustment.rightSide ≫
    ((UniversalSourceInterval.parametricNaturalitySquare specification.{u} v).h ≫
      (PointedMapping.coordinateMap (mappingIso Z).inv
        (PointedObject.basedHomMap P (mappingIso Z').hom)).right) = _
  rw [← Category.assoc, UniversalSourceInterval.parametricNaturalitySquare_finish, SSet.const_comp]
  have hv := PointedMapping.coordinateMap_vertex (mappingIso Z).inv
    (PointedObject.basedHomMap P (mappingIso Z').hom)
    (PointedMapping.parametricPost source.{u} v ≫
      PointedObject.basedHomMap P (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed reversal.{u} Z'))
  have he := mappingIso_parametric_conjugate_pre v reversal.{u} _
    (TwoLoopSource.mappingIso_pre_reversal PointedSimplicialSet.circle.{u} Z')
  exact (congrArg (fun x => SSet.const (X := (Δ[1] : SSet.{u})) x) hv).trans
    (congrArg (fun f => SSet.const (PointedMapping.familyVertex f)) he)

end SerrePositivity.KST.Spectra.OrdinaryLoopSource
