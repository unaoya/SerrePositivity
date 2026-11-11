module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.SmallUnstraighteningRelativeVertex
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorIsoPointEvaluation
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.UniverseHomotopyDownNaturality

/-!
概要：小宇宙の実際の相対頂点比較から端点正規化を外し、始域制限と交換させる。
方針：元の相対同型の縮小と下降を保ち、下降関手の自然性を適用する。
規約：指定同型の類を保持。使われ方：小さい全空間の三角形比較の fiber 制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  {f g : leftUnstraightening F ⟶ leftUnstraightening G}
  (hf : f ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
  (hg : g ≫ leftUnstraighteningProjection G = leftUnstraighteningProjection F)
  (e : VertexIso (relativeFunctorVertex _ _ f hf) (relativeFunctorVertex _ _ g hg))

/-- 小さい指定比較は元の比較の同じ像の下降の端点正規化。 -/
lemma smallRelativeVertexIso_heq_down_map :
    HEq (smallUnstraighteningRelativeVertexIso F G hf hg e)
      (downVertexIso (VertexIso.map e (smallLeftUnstraighteningRelativeFunctorIso F G).inv)) := by
  unfold smallUnstraighteningRelativeVertexIso
  dsimp only
  exact iso_endpoints_heq _ _ _

/-- 小さい指定比較の始域制限は元の指定像の持ち上げた制限の下降。 -/
lemma smallRelativeVertexIso_pre_heq_down_map {C : SSet.{u}}
    (s : C ⟶ smallLeftUnstraightening F) :
    HEq
      (VertexIso.map (smallUnstraighteningRelativeVertexIso F G hf hg e)
        (relativeFunctorPre (smallLeftUnstraighteningProjection G)
          (smallLeftUnstraighteningProjection F) s))
      (downVertexIso
        (VertexIso.map (VertexIso.map e (smallLeftUnstraighteningRelativeFunctorIso F G).inv)
          ((SSet.uliftFunctor.{u + 1, u}).map
            (relativeFunctorPre (smallLeftUnstraighteningProjection G)
              (smallLeftUnstraighteningProjection F) s)))) := by
  have hm := vertexIso_map_heq_of_heq (smallUnstraighteningRelativeVertexIso F G hf hg e)
    (downVertexIso (VertexIso.map e (smallLeftUnstraighteningRelativeFunctorIso F G).inv))
    (congrArg ULift.down (smallUnstraighteningRelativeIso_inv_vertex F G f hf)).symm
    (congrArg ULift.down (smallUnstraighteningRelativeIso_inv_vertex F G g hg)).symm
    (smallRelativeVertexIso_heq_down_map F G hf hg e)
    (relativeFunctorPre (smallLeftUnstraighteningProjection G)
      (smallLeftUnstraighteningProjection F) s)
  exact hm.trans (heq_of_eq (downVertexIso_map _ _))

end SerrePositivity.InfinityCategories.F2
