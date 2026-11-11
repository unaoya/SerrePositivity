module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UliftHomotopyIsoDown
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.QCatEquivalence
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative

/-!
概要：既存の指定関手同型の宇宙持ち上げを下降すると、元の指定値を回収する。
方針：既存の持ち上げを同じ全円柱の指定同型で表示し、その下降と代表の仕様を使う。
規約：Kan 標的、元の指定同型を保持。使われ方：native cospan の可換同型の下降。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 既存の指定同型の宇宙持ち上げの下降は、同じ元の同型に厳密に一致する。 -/
lemma functorIsoDown_ulift_iso {X Y : SSet.{u}} [KanComplex Y]
    {f g : X ⟶ Y} (e : FunctorIso f g) : functorIsoDown e.ulift.{u, v} = e := by
  have hu : e.ulift.{u, v} = functorIsoOfSimplicialHomotopy
      (uliftSimplicialHomotopy.{u, v} e.simplicialHomotopy) := by
    apply Iso.ext
    rfl
  rw [hu, functorIsoDown_uliftHomotopy]
  apply Iso.ext
  exact functorHomHomotopy_hom e.hom

end SerrePositivity.InfinityCategories.F2
