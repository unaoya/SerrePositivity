module

public import SerrePositivity.KST.Spectra.OrdinaryLoopParametricNaturality
public import SerrePositivity.KST.Spectra.TwoLoopSourceParametricPost

/-!
概要：共役で作った通常円の全族作用を、標準の三つの ihomAction の反復へ厳密同定する。
方針：同じ二重 curry の全族自然性で共役を打ち消し、元の実正方形を同じ二辺へ戻す。
規約：同じ区間・二次元射・全境界を保持。使われ方：元の随伴への標準全族 trace 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.OrdinaryLoopSource
variable {P Z Z' : PointedSimplicialSet.{u}} (v : P ⟶ PointedObject.basedHom Z Z')

/-- 共役した全族作用は、元の内側の円と外側二円の標準反復作用そのもの。 -/
lemma parametricLoopPost_eq_standard :
    parametricLoopPost v =
      TwoLoopSource.standardParametricPost PointedSimplicialSet.circle.{u} v := by
  change (TwoLoopSource.mappingIso PointedSimplicialSet.circle.{u} Z).inv ≫
      (PointedMapping.parametricPost (TwoLoopSource.source PointedSimplicialSet.circle.{u}) v ≫
        PointedObject.basedHomMap P (TwoLoopSource.mappingIso
          PointedSimplicialSet.circle.{u} Z').hom) = _
  rw [TwoLoopSource.mappingIso_standardParametricPost, Iso.inv_hom_id_assoc]

/-- 同じ作用を標準の三つの ihomAction の転置として、全単体の射の等式で表示する。 -/
lemma parametricLoopPost_standardFormula :
    parametricLoopPost v = PointedMapping.transpose (v ≫
      PointedMapping.ihomAction PointedSimplicialSet.circle.{u} Z Z' ≫
      PointedMapping.ihomAction CirclePower.space.{u}
        (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)
        (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z') ≫
      PointedMapping.ihomAction CirclePower.space.{u}
        (PointedObject.basedHom CirclePower.space.{u}
          (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z))
        (PointedObject.basedHom CirclePower.space.{u}
          (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z'))) := by
  rw [parametricLoopPost_eq_standard]
  simp only [TwoLoopSource.standardParametricPost, PointedMapping.parametricPost, Category.assoc]

variable [KanComplex Z.right] [KanComplex Z'.right]

/-- 現在の元の交換区間の、標準反復作用に対する同じ全パラメータ実自然性正方形。 -/
def loopExchangeStandardParametricNaturalitySquare :
    SSet.Homotopy (((loopExchangeInterval Z).basedPost
      (TwoLoopSource.standardParametricPost PointedSimplicialSet.circle.{u} v)).path)
      ((((loopExchangeInterval Z').basedIhomMap P).pre
        (TwoLoopSource.standardParametricPost PointedSimplicialSet.circle.{u} v)).path) where
  h := (loopExchangeParametricNaturalitySquare v).h
  h₀ := by
    rw [← parametricLoopPost_eq_standard v]
    exact (loopExchangeParametricNaturalitySquare v).h₀
  h₁ := by
    rw [← parametricLoopPost_eq_standard v]
    exact (loopExchangeParametricNaturalitySquare v).h₁
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

/-- 左境界全体も、標準反復作用と元の交換頂点の合成で一定。 -/
lemma loopExchangeStandardParametricNaturalitySquare_start :
    SquareAdjustment.leftSide ≫ (loopExchangeStandardParametricNaturalitySquare v).h =
      SSet.const (PointedMapping.familyVertex
        (TwoLoopSource.standardParametricPost PointedSimplicialSet.circle.{u} v ≫
          PointedObject.basedHomMap P (LoopExchangePaths.swap
            (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z')))) := by
  exact (loopExchangeParametricNaturalitySquare_start v).trans
    (congrArg (fun m => SSet.const (PointedMapping.familyVertex (m ≫
      PointedObject.basedHomMap P (LoopExchangePaths.swap
        (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z')))))
      (parametricLoopPost_eq_standard v))

/-- 右境界全体も、標準反復作用と元の反転頂点の合成で一定。 -/
lemma loopExchangeStandardParametricNaturalitySquare_finish :
    SquareAdjustment.rightSide ≫ (loopExchangeStandardParametricNaturalitySquare v).h =
      SSet.const (PointedMapping.familyVertex
        (TwoLoopSource.standardParametricPost PointedSimplicialSet.circle.{u} v ≫
          PointedObject.basedHomMap P (LoopExchangePaths.reversal
            (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z')))) := by
  exact (loopExchangeParametricNaturalitySquare_finish v).trans
    (congrArg (fun m => SSet.const (PointedMapping.familyVertex (m ≫
      PointedObject.basedHomMap P (LoopExchangePaths.reversal
        (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z')))))
      (parametricLoopPost_eq_standard v))

end SerrePositivity.KST.Spectra.OrdinaryLoopSource
