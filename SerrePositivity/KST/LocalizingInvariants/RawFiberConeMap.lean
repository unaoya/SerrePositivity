module

public import SerrePositivity.KST.LocalizingInvariants.FibrationFiberMap
public import SerrePositivity.KST.LocalizingInvariants.RawFiberInfinityCone
public import SerrePositivity.KST.LocalizingInvariants.StrictConeMap

/-!
概要：厳密 BF 正方形の fiber 比較を、置換前の実 fiber と全 cospan 錐の比較にする。
方針：段ごとの fiber 射を束ね、包含と置換比較の厳密自然性を確認して全錐へ拡張する。
規約：整数接続射で使う同じ比較射を保持。使われ方：元の pullback cube との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum

namespace SerrePositivity.KST.LocalizingInvariants.RawFiberComparison

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  [hp : ∀ n, Fibration (p.app n).right] [hq : ∀ n, Fibration (q.app n).right]
  (a : X ⟶ X') (b : Y ⟶ Y') (h : p ≫ b = a ≫ q)

def map : FiberModel.obj p hp ⟶ FiberModel.obj q hq where
  app := (FibrationFiberComparison.sequenceMap p q a b h).app
  comm := (FibrationFiberComparison.sequenceMap p q a b h).comm

lemma map_inclusion : map p q a b h ≫ FiberModel.inclusion q hq =
    FiberModel.inclusion p hp ≫ a :=
  OmegaSpectrum.Hom.ext (fun n ↦ FibrationFiberComparison.level_ι p q a b h n)

lemma comparison_natural : FibrationFiberComparison.map p q a b h ≫ FiberModel.comparison q hq =
    FiberModel.comparison p hp ≫ map p q a b h :=
  OmegaSpectrum.Hom.ext (fun n ↦ FibrationFiberComparison.map_level p q a b h n)

omit hp hq in
def ordinaryDiagramMap : cospan p (fromPoint Y) ⟶ cospan q (fromPoint Y') :=
  cospanHomMk b a (𝟙 _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint) h (point_isInitial.hom_ext _ _)

def diagramMap : _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram p (fromPoint Y) ⟶
    _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPullbackDiagram q (fromPoint Y') :=
  Functor.whiskerLeft AsSmall.down (ordinaryDiagramMap p q a b h)

lemma cone_condition (i : AsSmall.{u} WalkingCospan) :
    (FiberModel.smallCone p).π.app i ≫ (diagramMap p q a b h).app i =
      map p q a b h ≫ (FiberModel.smallCone q).π.app i := by
  rcases i with ⟨_ | (_ | _)⟩
  · change (FiberModel.inclusion p hp ≫ p) ≫ b =
      map p q a b h ≫ (FiberModel.inclusion q hq ≫ q)
    rw [← Category.assoc, map_inclusion]
    simpa only [Category.assoc] using
      congrArg (fun r ↦ FiberModel.inclusion p hp ≫ r) h
  · exact (map_inclusion p q a b h).symm
  · exact _root_.SerrePositivity.InfinityCategories.HomotopyLimits.spectrumPoint_isTerminal.hom_ext _ _

def coneTransformation : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictConeFunctor (FiberModel.smallCone p) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictConeFunctor (FiberModel.smallCone q) :=
  StrictConeMap.transformation (diagramMap p q a b h) _ _ (map p q a b h)
    (cone_condition p q a b h)

lemma coneTransformation_star : (coneTransformation p q a b h).app WithInitial.star =
    map p q a b h := rfl

end SerrePositivity.KST.LocalizingInvariants.RawFiberComparison
