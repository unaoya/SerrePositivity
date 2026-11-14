module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.ReflectiveLocalObjects
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.RestrictedPrecomposition

/-!
概要：反射は自身が反転する辺に関する局所化である。
方針：包含による制限を前合成の逆とし、余単位と反転関手上の単位で両合成を同型にする。
規約：任意の W に対する局所化の存在は主張しない。
使われ方：Kerodon §6.3.3（Tag 02FY） の反射的局所化と Def 6.3.1.9 の普遍性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-- 概要：h Fun の類が可逆なホモトピーは各点でも可逆。
方針：成分評価が同型を保つこととホモトピー成分の表示を使う。
規約：始域・標的の quasicategory 性は不要。
使われ方：反射で写した単位の成分の可逆性。 -/
lemma homotopy_component_isInvertible_of_isIso {A X : SSet.{u}} {f g : A ⟶ X}
    (H : SSet.Homotopy f g)
    [IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H))]
    (x : A _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated := by
  have h : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) x) :=
    inferInstance
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated)
  exact (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomEvaluate_homotopy H x) ▸ h

namespace ReflectiveSubcategory
variable {X : SSet.{u}} [Quasicategory X] {P : X _⦋0⦌ → Prop}
variable (r : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory X P)

/-- 概要：反射単位の選んだホモトピー代表の各成分は反射で反転される。
方針：反射で写した単位の h Fun の可逆性を成分へ移す。
規約：元の単位の代表を用いる。使われ方：反転関手上の単位による前合成の同型。 -/
lemma unitComponent_mem_invertedEdges (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy r.unit) x).edge ∈
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy r.unit) r.reflector
  haveI : IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy r.unit) r.reflector)))
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom]
    exact r.adjunction.unit_postcompLeft_isIso
  have h := homotopy_component_isInvertible_of_isIso H x
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy r.unit) x).edge).map
      ((truncation 2).map r.reflector))
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).toTruncated) rfl).mpr h

/-- 概要：反射が反転する辺を反転する関手族上の、単位による前合成の自然同型。
方針：各関手が全ての単位成分を反転することを制限付き前合成の一般補題へ渡す。
規約：元の圏の全対象を局所と仮定しない。使われ方：局所化の逆合成。 -/
def invertingUnitPrecompositionIso (E : SSet.{u}) [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector)).ι
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector)).ι ≫ (pre r.localization).app E) := by
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector)
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorIsoRestrictedPrecompositionOfHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy r.unit) K.ι (by
    intro v u hu x
    have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
    change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector) v.val at hv
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex at hv
    rw [show v.val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv X E) u from hu, Equiv.symm_apply_apply] at hv
    have hi := hv (r.unitComponent_mem_invertedEdges x)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy r.unit) x).edge).map ((truncation 2).map u))
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy r.unit) x).toTruncated.map
        ((truncation 2).map u)) rfl).mp hi)
  simpa only [pre_id, NatTrans.id_app, Category.comp_id] using h

/-- 概要：反射に沿う前合成の逆は包含に沿う制限。
方針：W を反転する関手を包含上で制限する。
規約：W は reflector 自身が反転する辺の集合。使われ方：局所化の普遍同値の逆射。 -/
def localizationRestriction (E : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector) : SSet.{u}) ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})).obj E :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector)).ι ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι).app E

/-- 概要：反射に沿う前合成と包含による制限は自然同値を与える。
方針：一方の合成は余単位、他方は反転関手上の単位で同型にする。
規約：局所化の存在を仮定せず、明示的な逆射を構成する。
使われ方：反射的局所化の普遍性。 -/
def localizationPrecompositionEquivalence (E : SSet.{u}) [Quasicategory E] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})).obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector) : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition r.reflector (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector) (fun _ h => h) E
  inv := r.localizationRestriction E
  homInvIso := by
    simpa only [localizationRestriction, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι,
      pre_map, NatTrans.comp_app, pre_id, NatTrans.id_app] using r.counitIso.map_pre E
  invHomIso := by
    let K := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector)
    let U := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition r.reflector (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector) (fun _ h => h) E
    let V := r.localizationRestriction E
    have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((𝟙 (K : SSet.{u})) ≫ K.ι) ((V ≫ U) ≫ K.ι) := by
      simpa only [V, U, K, localizationRestriction, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition_ι,
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.localization, pre_map, NatTrans.comp_app, Category.id_comp] using
        r.invertingUnitPrecompositionIso E
    let hf := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.fullSubcomplexFunctorInclusionHoFullyFaithful (K : SSet.{u}) ((ihom X).obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex X E (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector))
    exact (hf.preimageIso (X := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (𝟙 (K : SSet.{u}))))
      (Y := HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (V ≫ U))) h).symm

/-- 概要：反射は自身が反転する辺に関する局所化を表す。
方針：全標的での明示的な前合成の同値を局所化の定義へ渡す。
規約：任意の辺集合に対する局所化の存在は主張しない。
使われ方：Kerodon §6.3.3（Tag 02FY） の反射的局所化の普遍性。 -/
lemma isLocalization : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization r.reflector (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertedEdges r.reflector) := by
  refine ⟨fun _ h => h, fun E _ => ?_⟩
  exact (r.localizationPrecompositionEquivalence E).isQCatEquivalence

end ReflectiveSubcategory
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.3.4.3"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.isLocalization
attribute [cite HTT "5.2.7.12" (partial := special) "仮定：局所化が充満部分圏への反射 r として与えられ、任意の標的準圏 D を取る（Lean が強い：包含を右随伴として指定した形）。結論：元の全関手準圏で前合成が充満忠実で、本質像は反射が反転する全辺を反転する関手（この場合に一致）。明示的な逆と両往復の FunctorIso があり、core や関手の同値類の集合だけの普遍性ではない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.isLocalization
attribute [cite HTT "5.2.7.12" (partial := special) "仮定：局所化が充満部分圏への反射 r として与えられ、任意の標的準圏 D を取る（Lean が強い：包含を右随伴として指定した形）。結論：元の全関手準圏で前合成が充満忠実で、本質像は反射が反転する全辺を反転する関手（この場合に一致）。明示的な逆と両往復の FunctorIso があり、core や関手の同値類の集合だけの普遍性ではない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.localizationPrecompositionEquivalence
attribute [cite HTT "5.2.7.3" (partial := special) "仮定：充満包含への反射 r と任意の準圏 E（Lean が強い：右随伴が充満包含の形）。結論：r.reflector に沿う前合成は全関手圏で充満忠実で、その本質像は r.reflector が反転する全辺を反転する関手（この場合に一致）。明示的な QCatEquivalence が反転関手の全部分圏へ与えられる。一般の辺集合の局所化に右随伴があるという逆の主張は型に含めない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.isLocalization
attribute [cite HTT "5.2.7.3" (partial := special) "仮定：充満包含への反射 r と任意の準圏 E（Lean が強い：右随伴が充満包含の形）。結論：r.reflector に沿う前合成は全関手圏で充満忠実で、その本質像は r.reflector が反転する全辺を反転する関手（この場合に一致）。明示的な QCatEquivalence が反転関手の全部分圏へ与えられる。一般の辺集合の局所化に右随伴があるという逆の主張は型に含めない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ReflectiveSubcategory.localizationPrecompositionEquivalence
