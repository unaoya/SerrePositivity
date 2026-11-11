module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.DiscreteLimitComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LocalizationInitial

/-!
概要：初頂点写像の局所化普遍性は任意の小余積で保存される。
方針：反転関手と全関手の極限錐の比較に、離散図式の同値不変性を適用する。
規約：空の族を含み、小余積の特定の表示に依存しない。
使われ方：骨格の各次数の境界・標準単体の族の貼り合わせ。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 離散図式の全ての頂点で初頂点写像が局所化なら、余極限でも局所化。 -/
lemma transportSimplexFirstVertexMap_isLocalization_of_discrete_colimit {I : Type u}
    {F : Discrete I ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap (F.obj j))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges (F.obj j))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap c.pt) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges c.pt) := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_inverts c.pt, fun E _ ↦ ?_⟩
  let S := F.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportBaseRestrictionDiagram E
  let T := F.op ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingDiagram E
  let η : S ⟶ T := Functor.whiskerLeft F.op (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexLocalizationComparison E)
  let s := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportBaseRestrictionDiagram E).mapCone c.op
  let t := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingDiagram E).mapCone c.op
  have hs : IsLimit s := isLimitOfPreserves (internalHom.flip.obj E) hc.op
  have ht : IsLimit t := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInvertingConeIsLimit hc E
  let e := (Discrete.opposite I).symm
  let L := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap c.pt)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges c.pt) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_inverts c.pt) E
  have hL (j : (Discrete I)ᵒᵖ) : L ≫ t.π.app j = s.π.app j ≫ η.app j :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexLocalizationPrecomposition_naturality (c.ι.app j.unop) E).symm
  have : ∀ j, Quasicategory ((e.functor ⋙ S).obj j) := by
    intro j
    change Quasicategory ((ihom (F.obj (e.functor.obj j).unop)).obj E)
    infer_instance
  have : ∀ j, Quasicategory ((e.functor ⋙ T).obj j) := by
    intro j
    change Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
      ((ihom (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (F.obj (e.functor.obj j).unop)))).obj E)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsInvertingFunctorVertex _ E (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges (F.obj (e.functor.obj j).unop))) :
      SSet.{u})
    infer_instance
  have hη : ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((Functor.whiskerLeft e.functor η).app j) := by
    intro j
    obtain ⟨_, hj⟩ := hF (e.functor.obj j).unop
    exact hj E
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence L :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPrecompositionEquivalence_discreteConeMap (Functor.whiskerLeft e.functor η) hη
      (s.whisker e.functor) (t.whisker e.functor)
      (hs.whiskerEquivalence e) (ht.whiskerEquivalence e) L (fun j ↦ hL (e.functor.obj j))
  exact he.isQCatEquivalence

/-- 初頂点写像の局所化普遍性は、空の族を含む任意の小余積で保存される。 -/
lemma transportSimplexFirstVertexMap_isLocalization_coproduct {I : Type u}
    (X : I → SSet.{u})
    (hX : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap (X i))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges (X i))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap (∐ X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexInitialEdges (∐ X)) :=
  transportSimplexFirstVertexMap_isLocalization_of_discrete_colimit
    (colimit.isColimit (Discrete.functor X)) (fun j ↦ hX j.as)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
