module

public import SerrePositivity.InfinityCategories.F2.Ind.ParametrizedRestrictionLifting

/-!
概要：left anodyne な制限による、元のパラメータ付き切断の全境界持ち上げ。
方針：F1 の相対内部 Hom の持ち上げを、そのまま元の底の族に移す。
規約：新しい同値性を仮定しない。使われ方：under 圏の初頂点での評価の同値性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の left fibration の族の left anodyne な制限は trivial Kan fibration。 -/
lemma parametrizedSectionsPre_trivialKanFibration {A D E Y P : SSet.{u}} (p : E ⟶ Y)
    [LeftFibration p] (a : P ⟶ (ihom A).obj Y) (b : P ⟶ (ihom D).obj Y) (i : D ⟶ A)
    (h : a ≫ (pre i).app Y = b) (hi : leftAnodyneExtensions i) :
    TrivialKanFibration (parametrizedSectionsPre p a b i h) := by
  let sq' := CategoryTheory.Functor.PullbackObjObj.ofHasPullback internalHom i p
  have := trivialKanFibration_relativeHom_of_leftAnodyne i hi p sq'
  exact parametrizedSectionsPre_trivial_of_relativeHom p a b i h sq'

end SerrePositivity.InfinityCategories.F2.Ind
