module


public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexComparison

/-!
概要：第一終点を固定し、第二終点を動かす分母付き span の実 ∞ 圏。
方針：第一終点評価の inner fibration 性を、頂点制限の実単射から導く。
規約：第二終点射影の cocartesian 性とその局所的 cartesian 性は後続。
使われ方：分数写像空間の族を一つの ∞ 圏として解析する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

lemma evaluation_restriction_unit {K X : SSet.{u}} (v : K _⦋0⦌) :
    (pre (SSet.const (X := 𝟙_ SSet.{u}) v)).app X ≫ (unitIsoSelf (X := X)).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  rfl

lemma evaluation_innerFibration {K X : SSet.{u}} [Quasicategory X] (v : K _⦋0⦌) :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := X) v) := by
  let c := SSet.const (X := 𝟙_ SSet.{u}) v
  have : Mono c := Limits.IsTerminal.mono_from
    CartesianMonoidalCategory.isTerminalTensorUnit c
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.evaluation_restriction_unit]
  exact ⟨innerFibrations.comp_mem _ _ (mem_innerFibrations _)
    (MorphismProperty.rlp_of_isIso _ _)⟩

instance markedSpanSource_innerFibration (X : SSet.{u}) [Quasicategory X]
    (W : Set (X _⦋1⦌)) : InnerFibration (markedSpanSource X W) := by
  rw [← markedSpanBoundary_source]
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.evaluation_innerFibration (K := (boundary 1 : SSet.{u})) (X := X)
    (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 2), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary 0 0⟩ :
      (boundary 1 : SSet.{u}) _⦋0⦌)
  exact ⟨innerFibrations.comp_mem _ _ (mem_innerFibrations _) (mem_innerFibrations _)⟩

def markedSpanFamily (X : SSet.{u}) (W : Set (X _⦋1⦌)) (x : X _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (markedSpanSource X W) x

instance markedSpanFamily_quasicategory (X : SSet.{u}) [Quasicategory X]
    (W : Set (X _⦋1⦌)) (x : X _⦋0⦌) : Quasicategory (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.innerFibration_vertexFiber_quasicategory _ _

def markedSpanFamilyProjection (X : SSet.{u}) (W : Set (X _⦋1⦌)) (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x ⟶ X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫ markedSpanTarget X W

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
