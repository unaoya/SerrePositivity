module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompletionOppositeGeneral
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LocalizationUlift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.NerveOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PreservedColimitComposition

/-!
概要：反対 transport 単体圏の最後の頂点写像による前合成は充満忠実。
方針：初頂点の局所化を内部 Hom の反転同型と nerve の反転同型で移す。
規約：底の quasicategory 性やモデル圏の instance を要求しない。
使われ方：有限段階に沿う局所左 Kan の保存余極限を元の形状へ移す。

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

/-- 概要：全標的で充満忠実な前合成は添字の反転でも充満忠実。
方針：内部 Hom の反転同型で前合成を挟み、二重反転を消す。
規約：添字の quasicategory 性は不要。使われ方：初頂点局所化の反転。 -/
lemma fullyFaithful_pre_op {A B : SSet.{u}} (f : A ⟶ B)
    (hf : ∀ (C : SSet.{u}) [Quasicategory C], _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre f).app C))
    (C : SSet.{u}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre (SSet.opFunctor.map f)).app C) := by
  have aux (D : SSet.{u}) [Quasicategory D] :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre (SSet.opFunctor.map f)).app D.op) := by
    have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.isFullyFaithful_op_of_fullyFaithful _ (hf D)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso A D)).isQCatEquivalence.isFullyFaithful
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (SSet.opFunctor.map ((pre f).app D) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso A D).hom) at h
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHom_pre] at h
    have h' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso B D).symm).isQCatEquivalence.isFullyFaithful.comp h
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso B D).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso B D).hom ≫
        (pre (SSet.opFunctor.map f)).app D.op) at h'
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h'
  have transport (Y Z : SSet.{u}) [Quasicategory Y] [Quasicategory Z] (h : Y = Z) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre (SSet.opFunctor.map f)).app Y) →
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre (SSet.opFunctor.map f)).app Z) := by
    subst Z
    exact fun h ↦ h
  exact transport C.op.op C
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.opposite_opposite_eq C) (aux C.op)

/-- 概要：反対単体圏の最後の頂点写像。
方針：反転した底の初頂点写像を反転し、nerve と二重反転の同型で挟む。
規約：始域は反転した底の反対 transport 単体圏の nerve。
使われ方：段階関手の向きと余極限の向きを揃える。 -/
def transportSimplexLastVertexMap (B : SSet.{u}) :
    nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B.op)ᵒᵖ ⟶ B :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B.op)).inv ≫
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.op) ≫
      (SSet.opFunctorCompOpFunctorIso.app B).hom

/-- 概要：宇宙変更した最後の頂点写像による前合成は充満忠実。
方針：初頂点の宇宙変更版の局所化と反転による前合成の充満忠実性を使う。
規約：標的のみ quasicategory と仮定する。
使われ方：元の図式と反対単体圏に制限した図式の余錐比較。 -/
lemma transportSimplexLastVertexMap_ulift_pre_fullyFaithful (B : SSet.{u})
    (C : SSet.{max u v}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful
      ((pre ((SSet.uliftFunctor.{v, u}).map (transportSimplexLastVertexMap B))).app C) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre ((SSet.uliftFunctor.{v, u}).map
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.op)))).app C) := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre (SSet.opFunctor.map
      ((SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.op)))).app C)
    exact fullyFaithful_pre_op _
      (fun D _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.localization_pre_isFullyFaithful
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.transportSimplexFirstVertexMap_ulift_isLocalization.{u, v} B.op) D) C
  let e₁ := (SSet.uliftFunctor.{v, u}).mapIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.nerveOppositeIso (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B.op)).symm
  let e₂ := (SSet.uliftFunctor.{v, u}).mapIso (SSet.opFunctorCompOpFunctorIso.app B)
  have h₁ := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e₁) C).isFullyFaithful
  have h₂ := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso e₂) C).isFullyFaithful
  have hh := (h₂.comp h).comp h₁
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre e₂.hom).app C ≫
    (pre ((SSet.uliftFunctor.{v, u}).map
      (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.op)))).app C ≫
        (pre e₁.hom).app C) at hh
  simpa only [transportSimplexLastVertexMap, CategoryTheory.Functor.map_comp,
    pre_map, NatTrans.comp_app, Category.assoc, e₁, e₂,
    CategoryTheory.Functor.mapIso_hom, Iso.symm_hom] using hh

/-- 概要：最後の頂点への制限は元の図式の保存余極限を検出する。
方針：両標的で前合成の充満忠実性から全余錐の同値を使う。
規約：元の図式とその像を同時に比較する。
使われ方：反対単体圏で構成した保存余極限を元の形状へ戻す。 -/
lemma hasPreservedColimit_iff_lastVertexRestriction
    {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]
    (U : X ⟶ Y) (B : SSet.{u})
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexLastVertexMap B) ≫ F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_iff_nativeRestriction F _ U
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sliceUnderRestrict_isQCatEquivalence_of_fullyFaithful_pre _
      (transportSimplexLastVertexMap_ulift_pre_fullyFaithful B X) F)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.sliceUnderRestrict_isQCatEquivalence_of_fullyFaithful_pre _
      (transportSimplexLastVertexMap_ulift_pre_fullyFaithful B Y) (F ≫ U))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
