module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveLocalization

/-!
概要：可逆な余単位を持つ実随伴の左関手の局所化普遍性。
方針：右随伴による制限を前合成の逆とし、元の単位と余単位で両合成を比較する。
規約：商の普遍性を入力しない。使われ方：K-8 の半直交分解からの Verdier 列。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.AdjointLocalization
end SerrePositivity.KST.LocalizingInvariants.AdjointLocalization
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open _root_.SerrePositivity.KST.LocalizingInvariants.AdjointLocalization

variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) [IsIso a.counit]

local instance counitHomIsIso : IsIso a.counitHom := by
  change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatHomFunctor Y Y).map a.counit)
  infer_instance

def counitIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (G ≫ F) (𝟙 Y) := asIso a.counitHom

/-- 概要：左随伴単位の選んだホモトピー代表の各成分は左随伴で反転される。
方針：左随伴で写した単位の h Fun の可逆性を成分へ移す。
規約：元の単位の代表を用いる。使われ方：反転関手上の単位による前合成の同型。 -/
lemma unitComponent_mem_invertedEdges (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom) x).edge ∈
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom) F
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom) F)))
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom]
    exact a.unit_postcompLeft_isIso
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.homotopy_component_isInvertible_of_isIso H x
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom) x).edge).map
      ((truncation 2).map F))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated) rfl).mpr h

/-- 概要：左随伴が反転する辺を反転する関手族上の、単位による前合成の自然同型。
方針：各関手が全ての単位成分を反転することを制限付き前合成の一般補題へ渡す。
規約：元の圏の全対象を局所と仮定しない。使われ方：局所化の逆合成。 -/
def invertingUnitPrecompositionIso (E : SSet.{u}) [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F)).ι
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F)).ι ≫ (pre (F ≫ G)).app E) := by
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F)
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoRestrictedPrecompositionOfHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom) K.ι (by
    intro v u hu x
    have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F) v.val at hv
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex at hv
    rw [show v.val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X E) u from hu, Equiv.symm_apply_apply] at hv
    have hi := hv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.unitComponent_mem_invertedEdges a x)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom) x).edge).map
        ((truncation 2).map u))
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom) x).toTruncated.map
        ((truncation 2).map u)) rfl).mp hi)
  simpa only [pre_id, NatTrans.id_app, Category.comp_id] using h

/-- 概要：左随伴に沿う前合成の逆は右随伴に沿う制限。
方針：W を反転する関手を右随伴上で制限する。
規約：W は reflector 自身が反転する辺の集合。使われ方：局所化の普遍同値の逆射。 -/
def localizationRestriction (_a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (E : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F) : SSet.{u}) ⟶
      (ihom Y).obj E :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F)).ι ≫
    (pre G).app E

/-- 概要：左随伴に沿う前合成と右随伴による制限は自然同値を与える。
方針：一方の合成は余単位、他方は反転関手上の単位で同型にする。
規約：局所化の存在を仮定せず、明示的な逆射を構成する。
使われ方：左随伴的局所化の普遍性。 -/
def localizationPrecompositionEquivalence (E : SSet.{u}) [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((ihom Y).obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F) : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition F (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F) (fun _ h => h) E
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationRestriction a E
  homInvIso := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationRestriction, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι,
      pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.counitIso a).map_pre E
  invHomIso := by
    let K := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F)
    let U := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition F (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F) (fun _ h => h) E
    let V := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationRestriction a E
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((𝟙 (K : SSet.{u})) ≫ K.ι) ((V ≫ U) ≫ K.ι) := by
      simpa only [V, U, K, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationRestriction, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι,
        pre_map, NatTrans.comp_app, Category.id_comp] using
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingUnitPrecompositionIso a E
    let hf := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.fullSubcomplexFunctorInclusionHoFullyFaithful (K : SSet.{u}) ((ihom X).obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F))
    exact (hf.preimageIso (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 (K : SSet.{u}))))
      (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (V ≫ U))) h).symm

include a

/-- 概要：左随伴は自身が反転する辺に関する局所化を表す。
方針：全標的での明示的な前合成の同値を局所化の定義へ渡す。
規約：任意の辺集合に対する局所化の存在は主張しない。
使われ方：Kerodon §6.3.3（Tag 02FY） の左随伴的局所化の普遍性。 -/
lemma isLocalization : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization F (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges F) := by
  refine ⟨fun _ h => h, fun E _ => ?_⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecompositionEquivalence a E).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
