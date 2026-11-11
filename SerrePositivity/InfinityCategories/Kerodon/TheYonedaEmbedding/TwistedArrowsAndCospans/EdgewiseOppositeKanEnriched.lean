module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseKanEnriched
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.OppositeKanHomotopy

/-!
概要：edgewise な Hom から反転した Kan 複体の Hom への豊穣作用。
方針：内部 Hom の評価を反転し、Hom の edgewise 解像の左端射影をパラメーターに使う。
規約：通常の射の向きは変えず、単体の頂点順序を反転する。
使われ方：Kerodon §8.1.1（Tag 03JF）、Corollary 5.6.0.6（Tag 028T）、左右の係数を大域的に比較する終域側。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：反転した対象と反転した内部 Hom のパラメーターを評価する。
方針：直積の反転の標準同型を使い、元の評価の反転へ送る。
規約：X と Y の Kan 性は要求しない。
使われ方：Kerodon §8.1.1（Tag 03JF）、反転した Kan 複体への高次の作用の評価。 -/
def oppositeInternalHomEvaluation (X Y : SSet.{u}) :
    X.op ⊗ ((ihom X).obj Y).op ⟶ Y.op :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.oppositeTensorIso X ((ihom X).obj Y)).inv ≫
    SSet.opFunctor.map ((ihom.ev X).app Y)

/-- 概要：反転した対象に edgewise な内部 Hom のパラメーターを作用させる。
方針：Hom の左端射影を反転した評価のパラメーターに使う。
規約：パラメーターは元の Hom ではなくその共通解像。
使われ方：Kerodon §8.1.1（Tag 03JF）、反転した対象の豊穣作用の uncurry。 -/
def edgewiseOppositeInternalHomEvaluation (X Y : SSet.{u}) :
    X.op ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision ((ihom X).obj Y) ⟶ Y.op :=
  (X.op ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft ((ihom X).obj Y)) ≫ oppositeInternalHomEvaluation X Y

/-- 概要：Hom の共通解像は反転した二つの対象間の内部 Hom に作用する。
方針：左端射影を使う評価を curry する。
規約：全次数の実際の写像空間への作用。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、反転した係数の coherent な図式の Hom の作用。 -/
def edgewiseOppositeKanEnrichedMap (X Y : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision ((ihom X).obj Y) ⟶ (ihom X.op).obj Y.op :=
  curry (edgewiseOppositeInternalHomEvaluation X Y)

/-- 概要：Kan 複体の反転は Hom を解像した圏からの豊穣関手になる。
方針：左端での共通パラメーターの評価に単位・合成の計算則を適用する。
規約：通常の反転関手に元の Hom からの豊穣作用を仮定しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、左右の Hom の規約を一般の coherent な図式で比較する。 -/
def edgewiseOppositeKanEnriched :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.ConjugateAndDualFibrations.EdgewiseEnrichedObject _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} where
  obj X := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor.obj X.val
  map X Y := edgewiseOppositeKanEnrichedMap X.val.obj Y.val.obj
  map_id X := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, t⟩
    rfl
  map_comp X Y Z := by
    apply uncurry_injective
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨x, f, g⟩
    rfl

/-- 概要：対象の共通解像での評価は左端射影と可換。
方針：重みの左半分に制限した二つの射を反転した内部 Hom の評価へ入れる。
規約：同じ左半分と標準単体の反転同型を両因子に使う。
使われ方：Kerodon §8.1.1（Tag 03JF）、対象の共通解像と反転した対象の豊穣自然性。 -/
lemma edgewiseInternalHomEvaluation_left (X Y : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseInternalHomEvaluation X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft Y =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft X ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft ((ihom X).obj Y)) ≫ oppositeInternalHomEvaluation X Y := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, f⟩
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
