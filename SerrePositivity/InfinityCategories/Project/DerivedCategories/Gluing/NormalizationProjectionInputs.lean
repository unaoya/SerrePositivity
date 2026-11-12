module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationCompositionTetrahedron
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationAugmentationTriangles
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGCompositionTriangleFamily

/-! # 正規化側面の射影自然性の明示入力

概要：標準合成三角形の射影自然性だけを、上流から受け取る明示入力に隔離する。
方針：前後の実 slice 三角形と、射影した元二入力から作る標準三角形を比較する。
規約：Small 仮定や正本比較の同値性を入力に含めない。本体は上流からコピーしない。
使われ方：D の自然性入口で実例化し、共有面・側面を含む貼り合わせへ供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (E : Type (max u v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E))
  {K : SSet.{max u v}} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom R
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)) X Y)
local notation "Q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCommaObject R E E (DGFunctor.id E)
local notation "NX" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaObject R E X.replacement

/-- 概要：前正規化の全合成三角形が同じ射影で可換である条件。
方針：元閉射と元 Hom 入力を同じ dg 関手で写す。
規約：始域・標的の Small 性は要求しない。使われ方：前 cube の両側面の照合。 -/
def DGGluingPreNormalizeProjectionInput {Z : Type (max u v)} [_root_.SerrePositivity.DifferentialGraded.DGCategory R Z]
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R Q Z) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizePrism R E X Y f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R Z
      (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R Z
        (F.onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X))))
      (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map X Y))

/-- 概要：後正規化の全合成三角形が同じ射影で可換である条件。
方針：前正規化した同じ Hom 入力と元閉射を写す。
規約：元の二作用と primitive を変更しない。使われ方：後 cube の両側面の照合。 -/
def DGGluingPostNormalizeProjectionInput {Z : Type (max u v)} [_root_.SerrePositivity.DifferentialGraded.DGCategory R Z]
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R Q Z) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSlicePrismTriangle (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPostNormalizePrism R E X Y f) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R Z
      ((f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Q) (E := Q)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeHom R E X Y)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map NX Y))
      (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R Z
        (F.onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E Y))))

/-- 概要：元 Hom と終閉射の標準合成三角形についての射影自然性。
方針：正規化前の元入力と同じ終閉射を写す。
規約：四面体の第零面だけの自然性条件。使われ方：終側面を含む相対比較。 -/
def DGGluingExitProjectionInput {Z : Type (max u v)} [_root_.SerrePositivity.DifferentialGraded.DGCategory R Z]
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R Q Z) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingNormalizationExitTriangle R E X Y f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R Z
      (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (F.map X Y))
      (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R Z
        (F.onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E Y))))

/-- 概要：前後の三角形について必要な二射影の自然性をまとめる。
方針：上流から六つの全単体等式だけを受け取る。
規約：補助入力であり、正本比較の公開型を変更しない。
使われ方：D の Small 不要版が届くまで依存部分を明示的に隔離する。 -/
structure DGGluingNormalizationProjectionInput : Prop where
  preReplacement : DGGluingPreNormalizeProjectionInput R E X Y f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSourceLift R E E (DGFunctor.id E))
  preSource : DGGluingPreNormalizeProjectionInput R E X Y f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTargetLift R E E (DGFunctor.id E))
  postReplacement : DGGluingPostNormalizeProjectionInput R E X Y f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSourceLift R E E (DGFunctor.id E))
  postSource : DGGluingPostNormalizeProjectionInput R E X Y f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTargetLift R E E (DGFunctor.id E))
  exitReplacement : DGGluingExitProjectionInput R E X Y f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSourceLift R E E (DGFunctor.id E))
  exitSource : DGGluingExitProjectionInput R E X Y f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTargetLift R E E (DGFunctor.id E))

lemma dgGluingPreNormalizeAugmentationTriangle_projection_prereplacement
    (h : DGGluingNormalizationProjectionInput R E X Y f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] ⊗ K) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeAugmentationTriangle R E X Y f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max u v, max u v} E)
        (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R _
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSourceLift R E E (DGFunctor.id E)).onClosed.map
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X))))
        (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSourceLift R E E (DGFunctor.id E)).map X Y)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeAugmentationTriangle, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism_zero]
  exact h.preReplacement

lemma dgGluingPreNormalizeAugmentationTriangle_projection_presource
    (h : DGGluingNormalizationProjectionInput R E X Y f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ K) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeAugmentationTriangle R E X Y f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max u v, max u v} E)
        (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R _
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTargetLift R E E (DGFunctor.id E)).onClosed.map
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedIn R E X))))
        (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTargetLift R E E (DGFunctor.id E)).map X Y)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPreNormalizeAugmentationTriangle, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism_one]
  exact h.preSource

lemma dgGluingPostNormalizeAugmentationTriangle_projection_postreplacement
    (h : DGGluingNormalizationProjectionInput R E X Y f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (Δ[2] ⊗ K) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeAugmentationTriangle R E X Y f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max u v, max u v} E)
        ((f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Q) (E := Q)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeHom R E X Y)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSourceLift R E E (DGFunctor.id E)).map NX Y))
        (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R _
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationSourceLift R E E (DGFunctor.id E)).onClosed.map
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E Y)))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeAugmentationTriangle, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism_zero]
  exact h.postReplacement

lemma dgGluingPostNormalizeAugmentationTriangle_projection_postsource
    (h : DGGluingNormalizationProjectionInput R E X Y f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (Δ[2] ⊗ K) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeAugmentationTriangle R E X Y f =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDGCompositionTriangleFamily R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max u v, max u v} E)
        ((f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (D := Q) (E := Q)
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaPreNormalizeHom R E X Y)) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap
            ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTargetLift R E E (DGFunctor.id E)).map NX Y))
        (SSet.const (X := K) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedVertex R _
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCommaAugmentationTargetLift R E E (DGFunctor.id E)).onClosed.map
            (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingIdentityCommaNormalizationClosedOut R E Y)))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingPostNormalizeAugmentationTriangle, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommaAugmentationPrism_one]
  exact h.postSource

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
