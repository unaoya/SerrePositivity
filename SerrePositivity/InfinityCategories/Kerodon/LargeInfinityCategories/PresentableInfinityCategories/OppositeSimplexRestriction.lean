module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LastVertexPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertexNaturality

/-!
概要：反対単体圏から反転した底への局所化制限とその自然性を与える。
方針：nerve の反転同型と初頂点の自然性を合成する。
規約：二重反転の同一視を避け、元の反転した底へ写す。
使われ方：有限段階の包含と局所左 Kan の制限図式の厳密な比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：反対単体圏から反転した底への初頂点の反転。
方針：nerve の反転同型の逆と反転した初頂点写像を合成する。
規約：底の二重反転を消さない。使われ方：有限段階の自然な局所化。 -/
def oppositeSimplexRestriction (B : SSet.{u}) :
    nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)ᵒᵖ ⟶ B.op :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)).inv ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B)

/-- 概要：反対単体圏の制限は底の射について厳密に自然。
方針：nerve 反転の自然性を初頂点写像の自然性と合成する。
規約：反対圏と単体集合の反転を区別する。
使われ方：有限段階の制限図式を元の図式の制限と同定する。 -/
lemma oppositeSimplexRestriction_naturality {B D : SSet.{u}} (f : B ⟶ D) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor f).op ≫ oppositeSimplexRestriction D =
      oppositeSimplexRestriction B ≫ SSet.opFunctor.map f := by
  let eB := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)
  let eD := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory D)
  have hn : SSet.opFunctor.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor f)) ≫ eD.hom =
      eB.hom ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor f).op :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeMap_naturality _
  have hi : nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor f).op ≫ eD.inv =
      eB.inv ≫ SSet.opFunctor.map (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor f)) := by
    apply (cancel_mono eD.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn, Iso.inv_hom_id_assoc]
  change nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor f).op ≫ eD.inv ≫ _ =
    (eB.inv ≫ _) ≫ _
  rw [← Category.assoc, hi, Category.assoc, ← SSet.opFunctor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_naturality, SSet.opFunctor.map_comp, Category.assoc]

/-- 概要：宇宙変更後の反対単体圏への前合成は充満忠実。
方針：初頂点の局所化の反転と nerve の同型を合成する。
規約：底には quasicategory 性を要求しない。
使われ方：全余錐を両標的で同時に比較する。 -/
lemma oppositeSimplexRestriction_ulift_pre_fullyFaithful (B : SSet.{u})
    (C : SSet.{max u v}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful
      ((pre ((SSet.uliftFunctor.{v, u}).map (oppositeSimplexRestriction B))).app C) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre ((SSet.uliftFunctor.{v, u}).map
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B)))).app C) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre (SSet.opFunctor.map
      ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B)))).app C)
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fullyFaithful_pre_op _ (fun D _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localization_pre_isFullyFaithful
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_ulift_isLocalization.{u, v} B) D) C
  let e := (SSet.uliftFunctor.{v, u}).mapIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B)).symm
  have he := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e) C).isFullyFaithful
  have hh := h.comp he
  simpa only [oppositeSimplexRestriction, CategoryTheory.Functor.map_comp,
    pre_map, NatTrans.comp_app, e, CategoryTheory.Functor.mapIso_hom, Iso.symm_hom] using hh

/-- 概要：反対単体圏への制限は元の保存余極限を検出する。
方針：両標的で全余錐の同値を適用する。
規約：元の図式は反転した底を始域に持つ。
使われ方：有限段階の保存余極限を局所左 Kan の図式へ移す。 -/
lemma hasPreservedColimit_iff_oppositeSimplexRestriction
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (U : X ⟶ Y) (B : SSet.{u})
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B.op ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U
      ((SSet.uliftFunctor.{u + 1, u}).map (oppositeSimplexRestriction B) ≫ F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_iff_nativeRestriction F _ U
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sliceUnderRestrict_isQCatEquivalence_of_fullyFaithful_pre _
      (oppositeSimplexRestriction_ulift_pre_fullyFaithful B X) F)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sliceUnderRestrict_isQCatEquivalence_of_fullyFaithful_pre _
      (oppositeSimplexRestriction_ulift_pre_fullyFaithful B Y) (F ≫ U))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
