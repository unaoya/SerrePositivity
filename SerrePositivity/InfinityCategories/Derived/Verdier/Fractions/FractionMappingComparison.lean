module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants
variable {X Q : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : InvertsEdges F W) (x y : X _⦋0⦌)

def fractionMappingComparison : _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (fixedMarkedSpans X W x y) ⟶
    intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) :=
  localizationDescend _ _ (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion_isLocalization _) _
    (_root_.SerrePositivity.InfinityCategories.Derived.Localization.invertsAllEdges_toKan (fixedFractionEvaluation F W hF x y))

def fractionMappingComparisonIso : FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans X W x y) ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison F W hF x y)
    (fixedFractionEvaluation F W hF x y) :=
  localizationDescendIso _ _ (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion_isLocalization _) _
    (_root_.SerrePositivity.InfinityCategories.Derived.Localization.invertsAllEdges_toKan (fixedFractionEvaluation F W hF x y))

def fractionPinchedMappingComparison : _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (fixedMarkedSpans X W x y) ⟶
    pinchedHom (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y) :=
  localizationDescend _ _ (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion_isLocalization _) _
    (_root_.SerrePositivity.InfinityCategories.Derived.Localization.invertsAllEdges_toKan (fixedFractionPinchedEvaluation F W hF x y))

def fractionPinchedMappingComparisonIso : FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans X W x y) ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionPinchedMappingComparison F W hF x y) (fixedFractionPinchedEvaluation F W hF x y) :=
  localizationDescendIso _ _ (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion_isLocalization _) _
    (_root_.SerrePositivity.InfinityCategories.Derived.Localization.invertsAllEdges_toKan (fixedFractionPinchedEvaluation F W hF x y))

def fractionMappingModelComparisonIso : FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionPinchedMappingComparison F W hF x y ≫
      pinchedHomToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y))
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison F W hF x y) := by
  apply localizationFactorizationIso (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans X W x y))
    Set.univ (_root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion_isLocalization _)
  have h := FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionPinchedMappingComparisonIso F W hF x y)
      (pinchedHomToIntervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (F.app (Opposite.op ⦋0⦌) y)) ≪≫
    functorIsoOfSimplicialHomotopy (fixedFractionPinchedComparisonHomotopy F W hF x y) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparisonIso F W hF x y).symm
  simpa only [Category.assoc] using h

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionMappingComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparisonIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionMappingComparisonIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparisonIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingModelComparisonIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionMappingModelComparisonIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingModelComparisonIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionPinchedMappingComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionPinchedMappingComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionPinchedMappingComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionPinchedMappingComparisonIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionPinchedMappingComparisonIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionPinchedMappingComparisonIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionMappingComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionMappingComparison._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionMappingComparison._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionMappingComparison._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionMappingComparison.congr_simp := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionMappingModelComparisonIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingModelComparisonIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionMappingModelComparisonIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingModelComparisonIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionPinchedMappingComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionPinchedMappingComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionPinchedMappingComparison._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionPinchedMappingComparison._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionPinchedMappingComparison.congr_simp := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionPinchedMappingComparison.congr_simp
