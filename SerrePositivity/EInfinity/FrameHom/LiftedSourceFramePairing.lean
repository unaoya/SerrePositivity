module
public import SerrePositivity.EInfinity.FrameHom.LiftedSourceFrameElements
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingProjections

/-!
概要：同じ全source-frameの実射を、同じ元の両端を持つtwisted arrowへ送る。
方針：既存の全要素のdown・元の射・twisted pairingの全自然性を合成する。
規約：全射列・全単体作用素を保持する。augmentationの逆はまだ使わない。
使われ方：BEの元の同じ全要素から正本Homへのroof比較を組み立てる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
variable {C : Type u} [Category.{v} C]
  (Q : C ⥤ SimplexCategory ⥤ C) (R : C ⥤ C)

/-- 同じ全要素の元のsource-frameの始域を、同じHom宇宙に揃える。 -/
def liftedSourceFrameArrowDomain :
    SimplicialTotalElements (liftedSourceFrameCoefficients Q R) ⥤ (AsSmall.{max u v} C)ᵒᵖ :=
  liftedSourceFrameElementsDown Q R ⋙ sourceFrameArrowDomain Q R ⋙
    (AsSmall.up : C ⥤ AsSmall.{max u v} C).op

/-- 同じ全要素の元の実射の標的を、同じHom宇宙に揃える。 -/
def liftedSourceFrameArrowCodomain :
    SimplicialTotalElements (liftedSourceFrameCoefficients Q R) ⥤ AsSmall.{max u v} C :=
  liftedSourceFrameElementsDown Q R ⋙ sourceFrameArrowCodomain Q R ⋙ AsSmall.up

/-- 同じ全要素のラベルの元の実射を持ち上げる。 -/
def liftedSourceFrameArrowValue
    (X : SimplicialTotalElements (liftedSourceFrameCoefficients Q R)) :
    ((liftedSourceFrameArrowDomain Q R).obj X).unop ⟶
      (liftedSourceFrameArrowCodomain Q R).obj X :=
  AsSmall.up.map (sourceFrameArrowValue Q R ((liftedSourceFrameElementsDown Q R).obj X))

/-- 元の実射の同じ反変・共変の四角形は、全要素の任意の射で保たれる。 -/
theorem liftedSourceFrameArrowValue_naturality
    {X Y : SimplicialTotalElements (liftedSourceFrameCoefficients Q R)} (f : X ⟶ Y) :
    ((liftedSourceFrameArrowDomain Q R).map f).unop ≫ liftedSourceFrameArrowValue Q R X ≫
      (liftedSourceFrameArrowCodomain Q R).map f = liftedSourceFrameArrowValue Q R Y := by
  apply ULift.ext
  exact sourceFrameArrowValue_naturality Q R ((liftedSourceFrameElementsDown Q R).map f)

/-- 元の全要素の実射と同じ両端の、全単体に自然なtwisted pairing。 -/
def liftedSourceFramePairing :
    nerve (SimplicialTotalElements (liftedSourceFrameCoefficients Q R)) ⟶
      TwistedArrow (nerve (AsSmall.{max u v} C)) :=
  twistedPairingNerveMap (liftedSourceFrameArrowDomain Q R) (liftedSourceFrameArrowCodomain Q R)
    (liftedSourceFrameArrowValue Q R) (liftedSourceFrameArrowValue_naturality Q R)

/-- 同じ全pairingの二射影は、元の実射の同じ両端そのもの。 -/
theorem liftedSourceFramePairing_projection :
    liftedSourceFramePairing Q R ≫ twistedArrowProjection (nerve (AsSmall.{max u v} C)) =
      CartesianMonoidalCategory.lift
        (nerveMap (liftedSourceFrameArrowDomain Q R) ≫
          (nerveOppositeIso (C := AsSmall.{max u v} C)).inv)
        (nerveMap (liftedSourceFrameArrowCodomain Q R)) :=
  twistedPairingNerveMap_projection _ _ _ _
end SerrePositivity.EInfinity.FrameHom
