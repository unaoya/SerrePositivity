module

public import SerrePositivity.InfinityCategories.F2.Ind.CurryJointHomotopy
public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityTransformation
public import SerrePositivity.InfinityCategories.F2.Ind.ElementsDiagram
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering

/-!
概要：元の小さい Yoneda 図式から、元の F の定値図式への一つの自然変換を得る。
方針：宇宙持ち上げと積を交換し、同じ共同 Hom の自然変換を curry する。
規約：始域は固定済みの元の圏、図式は元の presheafElementsYonedaDiagram。
使われ方：F を指定頂点とする同じ小さい密度全余錐の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
local notation "E" => smallRightUnstraightening F
local notation "p" => smallRightUnstraighteningProjection F

/-- 同じ二変数の始域を curry すると、固定済みの元の Yoneda 図式そのもの。 -/
lemma presheafDensity_source_curry :
    curry ((HomotopyLimits.uliftTensorIso.{u, u + 1} C.op E).inv ≫
      twistedElementsHomDiagram p) = presheafElementsYonedaDiagram F := by
  apply uncurry_injective
  rw [uncurry_curry, presheafElementsYonedaDiagram, uncurry_natural_left,
    yonedaInfinityMap_uncurry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

omit [Quasicategory C] in
/-- 同じ二変数の標的を curry すると、元の F を値とする定値図式そのもの。 -/
lemma presheafDensity_target_curry :
    curry ((HomotopyLimits.uliftTensorIso.{u, u + 1} C.op E).inv ≫
      presheafTwistedElementsTargetDiagram F) = SSet.const (functorVertex F) := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_const_functorVertex]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 同じ元の Yoneda 図式から同じ F の定値図式への、全高次に整合する自然変換。 -/
def presheafDensityDiagramHomotopy :
    SSet.Homotopy (presheafElementsYonedaDiagram F) (SSet.const (functorVertex F)) := by
  have h := curryJointHomotopy
    (functorHomotopyPrecomp (presheafDensityJointHomotopy F)
      (HomotopyLimits.uliftTensorIso.{u, u + 1} C.op E).inv)
  rw [presheafDensity_source_curry, presheafDensity_target_curry] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Ind
