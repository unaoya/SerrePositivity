module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ReflectiveContinuousRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ReflectiveRepresentabilityDescent
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IndPresheafReflection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.ReflectiveLocality

/-!
概要：表現可能前層の辺作用による局所性判定を、一般の連続前層の表現可能性へ接続する。
方針：自由前層圏で得た表現の単位反転から局所性を得て、反映模型と元の同値に沿って降ろす。
規約：辺作用と Hom 前合成の比較は明示入力で、その存在をここで仮定へ隠さない。
使われ方：F1 の依頼済み比較界面が供給された後の d2 の接続。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：元の表現可能前層の辺の反転から Hom 前合成の局所性を回収する比較界面。
方針：同じ指定端点の実辺を両側に使う。
規約：宇宙変更後の反対辺の作用と元の Hom の局所性を区別する。
使われ方：反映単位の反転を局所な表現対象へ移すための F1 側の供給条件。 -/
def RepresentableInversionDetectsLocality (C : SSet.{u + 1}) [Quasicategory C] : Prop :=
  ∀ (z x y : C _⦋0⦌)
    (e : Truncated.Edge (X := (truncation 2).obj C) x y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u + 1, u + 2} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeOp e)).map
      ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.representablePresheafInfinity z))) →
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocalForHom (Truncated.HomotopyCategory.homMk e) z

/-- 概要：辺作用の比較界面の下で反映部分圏の連続前層は表現可能。
方針：自由前層圏の表現対象が全単位に局所であることを示し、同じ表現を降ろす。
規約：一般の局所化の存在は使わず、与えられた反映を使う。
使われ方：一般 presentable 圏の表現可能性の反映模型側の接続。 -/
lemma reflectiveContinuous_isRepresentable_of_inversionLocality
    {A : SSet.{u}} [Quasicategory A]
    (hLocal : RepresentableInversionDetectsLocality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A))
    {P : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) _⦋0⦌ → Prop}
    (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) P)
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A) P : SSet.{u + 1}).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.SendsSmallColimitsToLimits F) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor F := by
  obtain ⟨z, hz, hInv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reflectiveContinuous_exists_representation_inverting_units r F hF
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.reflective_isRepresentable_of_local_representation r F z _ hz
  apply (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.reflective_isLocal_iff_unit_local r z).mpr
  intro x
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitComponent r.unit x)
  rw [← he]
  exact hLocal z x (r.localization.app _ x) e (hInv x e he)

/-- 概要：自由前層圏の辺作用の比較界面から一般 presentable 圏の連続前層を表現する。
方針：既存の反映 Ind 模型へ制限し、局所な表現対象を元の全同値で戻す。
規約：表現対象と全自然同型は構成し、比較界面だけを明示入力にする。
使われ方：F1 の供給界面を d2 の一般の結論へ接続する。 -/
lemma presentableContinuous_isRepresentable_of_inversionLocality
    (hLocal : ∀ (A : SSet.{u}) [Quasicategory A],
      RepresentableInversionDetectsLocality (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PresheafInfinity A))
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (F : C.op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.SendsSmallColimitsToLimits F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.IsRepresentableSmallSpaceFunctor F := by
  obtain ⟨κ, hκ, A, hA, ⟨r⟩, ⟨e⟩⟩ := hC.exists_reflectiveIndModel
  have := hA
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isRepresentable_of_equivalence_restriction e F
  apply reflectiveContinuous_isRepresentable_of_inversionLocality (hLocal A) r
  exact hF.precomp_op e.hom (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.equivalence_preservesSmallColimits e.isQCatEquivalence)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
