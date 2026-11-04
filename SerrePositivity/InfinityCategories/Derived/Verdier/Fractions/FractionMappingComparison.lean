module

public import SerrePositivity.InfinityCategories.Derived.Localization.GroupoidCompletion
public import SerrePositivity.KST.LocalizingInvariants.FixedFractionPinchedEvaluation
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

/-!
概要：両端固定の分母付き span の ∞ 亜群化から、局所化後の写像空間へ実比較を構成する。
方針：実評価の標的が Kan 複体であることから全ての辺を反転し、局所化の普遍性で下ろす。
規約：比較の同値性は入力せず、未証明。使われ方：普遍 Ore 補完による写像空間の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : InvertsEdges F W) (x y : X _⦋0⦌)

def fractionMappingComparison : groupoidCompletion (fixedMarkedSpans X W x y) ⟶
    intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) :=
  localizationDescend _ _ (groupoidCompletion_isLocalization _) _
    (invertsAllEdges_toKan (fixedFractionEvaluation F W hF x y))

def fractionMappingComparisonIso : FunctorIso
    (groupoidCompletionMap (fixedMarkedSpans X W x y) ≫ fractionMappingComparison F W hF x y)
    (fixedFractionEvaluation F W hF x y) :=
  localizationDescendIso _ _ (groupoidCompletion_isLocalization _) _
    (invertsAllEdges_toKan (fixedFractionEvaluation F W hF x y))

def fractionPinchedMappingComparison : groupoidCompletion (fixedMarkedSpans X W x y) ⟶
    pinchedHom (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) :=
  localizationDescend _ _ (groupoidCompletion_isLocalization _) _
    (invertsAllEdges_toKan (fixedFractionPinchedEvaluation F W hF x y))

def fractionPinchedMappingComparisonIso : FunctorIso
    (groupoidCompletionMap (fixedMarkedSpans X W x y) ≫
      fractionPinchedMappingComparison F W hF x y) (fixedFractionPinchedEvaluation F W hF x y) :=
  localizationDescendIso _ _ (groupoidCompletion_isLocalization _) _
    (invertsAllEdges_toKan (fixedFractionPinchedEvaluation F W hF x y))

def fractionMappingModelComparisonIso : FunctorIso
    (fractionPinchedMappingComparison F W hF x y ≫
      pinchedHomToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y))
    (fractionMappingComparison F W hF x y) := by
  apply localizationFactorizationIso (groupoidCompletionMap (fixedMarkedSpans X W x y))
    Set.univ (groupoidCompletion_isLocalization _)
  have h := FunctorIso.postcomp (fractionPinchedMappingComparisonIso F W hF x y)
      (pinchedHomToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y)) ≪≫
    functorIsoOfSimplicialHomotopy (fixedFractionPinchedComparisonHomotopy F W hF x y) ≪≫
    (fractionMappingComparisonIso F W hF x y).symm
  simpa only [Category.assoc] using h

end SerrePositivity.KST.LocalizingInvariants
