module

public import SerrePositivity.InfinityCategories.F1.DiscreteLimitComparison
public import SerrePositivity.InfinityCategories.F1.TransportLocalizationInitial

/-!
概要：初頂点写像の局所化普遍性は任意の小余積で保存される。
方針：反転関手と全関手の極限錐の比較に、離散図式の同値不変性を適用する。
規約：空の族を含み、小余積の特定の表示に依存しない。
使われ方：骨格の各次数の境界・標準単体の族の貼り合わせ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 離散図式の全ての頂点で初頂点写像が局所化なら、余極限でも局所化。 -/
lemma transportSimplexFirstVertexMap_isLocalization_of_discrete_colimit {I : Type u}
    {F : Discrete I ⥤ SSet.{u}} {c : Cocone F} (hc : IsColimit c)
    (hF : ∀ j, IsLocalization (transportSimplexFirstVertexMap (F.obj j))
      (transportSimplexInitialEdges (F.obj j))) :
    IsLocalization (transportSimplexFirstVertexMap c.pt) (transportSimplexInitialEdges c.pt) := by
  refine ⟨transportSimplexFirstVertexMap_inverts c.pt, fun E _ ↦ ?_⟩
  let S := F.op ⋙ transportBaseRestrictionDiagram E
  let T := F.op ⋙ transportSimplexInvertingDiagram E
  let η : S ⟶ T := Functor.whiskerLeft F.op (transportSimplexLocalizationComparison E)
  let s := (transportBaseRestrictionDiagram E).mapCone c.op
  let t := (transportSimplexInvertingDiagram E).mapCone c.op
  have hs : IsLimit s := isLimitOfPreserves (internalHom.flip.obj E) hc.op
  have ht : IsLimit t := transportSimplexInvertingConeIsLimit hc E
  let e := (Discrete.opposite I).symm
  let L := localizationPrecomposition (transportSimplexFirstVertexMap c.pt)
    (transportSimplexInitialEdges c.pt) (transportSimplexFirstVertexMap_inverts c.pt) E
  have hL (j : (Discrete I)ᵒᵖ) : L ≫ t.π.app j = s.π.app j ≫ η.app j :=
    (transportSimplexLocalizationPrecomposition_naturality (c.ι.app j.unop) E).symm
  have : ∀ j, Quasicategory ((e.functor ⋙ S).obj j) := by
    intro j
    change Quasicategory ((ihom (F.obj (e.functor.obj j).unop)).obj E)
    infer_instance
  have : ∀ j, Quasicategory ((e.functor ⋙ T).obj j) := by
    intro j
    change Quasicategory (fullSubcomplexOnVertices
      ((ihom (nerve (TransportSimplexCategory (F.obj (e.functor.obj j).unop)))).obj E)
      (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges (F.obj (e.functor.obj j).unop))) :
      SSet.{u})
    infer_instance
  have hη : ∀ j, IsQCatEquivalence ((Functor.whiskerLeft e.functor η).app j) := by
    intro j
    obtain ⟨_, hj⟩ := hF (e.functor.obj j).unop
    exact hj E
  have he : IsPrecompositionEquivalence L :=
    isPrecompositionEquivalence_discreteConeMap (Functor.whiskerLeft e.functor η) hη
      (s.whisker e.functor) (t.whisker e.functor)
      (hs.whiskerEquivalence e) (ht.whiskerEquivalence e) L (fun j ↦ hL (e.functor.obj j))
  exact he.isQCatEquivalence

/-- 初頂点写像の局所化普遍性は、空の族を含む任意の小余積で保存される。 -/
lemma transportSimplexFirstVertexMap_isLocalization_coproduct {I : Type u}
    (X : I → SSet.{u})
    (hX : ∀ i, IsLocalization (transportSimplexFirstVertexMap (X i))
      (transportSimplexInitialEdges (X i))) :
    IsLocalization (transportSimplexFirstVertexMap (∐ X)) (transportSimplexInitialEdges (∐ X)) :=
  transportSimplexFirstVertexMap_isLocalization_of_discrete_colimit
    (colimit.isColimit (Discrete.functor X)) (fun j ↦ hX j.as)

end SerrePositivity.InfinityCategories
