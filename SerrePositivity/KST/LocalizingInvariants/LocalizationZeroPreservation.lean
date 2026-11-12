module

public import SerrePositivity.KST.LocalizingInvariants.LocalizationInitialPreservation
public import SerrePositivity.KST.LocalizingInvariants.LocalizationRightAdjunctionDescent
public import SerrePositivity.KST.LocalizingInvariants.PointTerminalAdjunction
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Pointed

/-!
概要：任意の辺集合の局所化は終対象と零対象を保ち、pointed な商を実際に与える。
方針：点への実左随伴の降下で終対象性を得て、証明済みの始対象保存と組み合わせる。
規約：安定性・完全性を仮定しない。使われ方：一般の Verdier 商候補の真の核。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma localization_preservesTerminal {X Q : SSet.{u}} [Quasicategory X] [Quasicategory Q]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W)
    (x : X _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (F.app (Opposite.op ⦋0⦌) x) := by
  let H : Q ⟶ (Δ[0] : SSet.{u}) := SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  let a := terminalPointAdjunction (F ≫ H) x hx
  let d := localizationRightAdjunctionDescent (SSet.const x) F H W hF a
  have h := pointAdjunction_isTerminal d (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (F.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 0)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at h
  exact h

lemma localization_preservesZero {X Q : SSet.{u}} [Quasicategory X] [Quasicategory Q]
    (F : X ⟶ Q) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W)
    (x : X _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex x) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌) x) :=
  ⟨localization_preservesInitial F W hF x hx.1, localization_preservesTerminal F W hF x hx.2⟩

instance edgeLocalization_hasZeroVertex (X : SSet.{u}) [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X]
    (W : Set (X _⦋1⦌)) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization X W) :=
  ⟨⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalizationMap X W).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).vertex,
    localization_preservesZero _ W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.edgeLocalization_isLocalization X W) _
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X).isZero⟩⟩

end SerrePositivity.KST.LocalizingInvariants
