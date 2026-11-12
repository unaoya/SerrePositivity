module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InverseAttachmentUniversal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerAnodyneReplacement
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：任意の辺集合の局所化を、実際の quasicategory と元の射として構成する。
方針：可逆区間の貼合せの全関手普遍性を、inner anodyne 置換の前合成同値で移す。
規約：局所化存在は結論。安定性・完全性・核の主張は後続で別途証明する。
使われ方：一般の Verdier 商と Land–Tamme の差の項の実構成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

lemma localization_postcomp_precompositionEquivalence {X P Q : SSet.{u}}
    (F : X ⟶ P) (W : Set (X _⦋1⦌)) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W)
    (j : P ⟶ Q) (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence j) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (F ≫ j) W := by
  obtain ⟨hF, hU⟩ := hF
  refine ⟨hF.comp j, fun Y _ => ?_⟩
  have hc : (pre j).app Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition F W hF Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (F ≫ j) W (hF.comp j) Y := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X Y W).ι).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι,
      pre_map, NatTrans.comp_app]
  rw [← hc]
  exact (hj Y).comp (hU Y)

/-- 任意の単体集合と任意の辺集合に対する、同じ宇宙内の実 quasicategory 局所化の存在。 -/
@[kerodon 01N0]
theorem exists_quasicategory_localization (X : SSet.{u}) (W : Set (X _⦋1⦌)) :
    ∃ (Q : SSet.{u}) (F : X ⟶ Q), Quasicategory Q ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F W := by
  let P := inverseAttachment X W
  let t : P ⟶ (Δ[0] : SSet.{u}) := SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  obtain ⟨Q, j, _, hj, hQ, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.exists_quasicategory_resolution_over t
  exact ⟨Q, inverseAttachmentInclusion X W ≫ j, hQ,
    localization_postcomp_precompositionEquivalence _ W (inverseAttachment_isLocalization X W)
      j (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne j hj)⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
