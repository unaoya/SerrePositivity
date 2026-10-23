module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpaceTensorProductProjection
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTransformationTotalMap

/-!
概要：点ごとの coherent 積図式の小さい全空間を、元の二つの全空間の引き戻しへ写す。
方針：指定射影の同じホモトピーから変換頂点を取り、元の全空間作用を組み合わせる。
規約：底は任意の小さい単体集合。使われ方：sifted 余極限と二項積の比較の始域。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 第一射影の指定ホモトピーが表す、元の変換空間の頂点。 -/
def coherentSpaceTensorProductFstVertex :
    (leftUnstraighteningTransformationSpace (coherentSpaceTensorProduct F G) F) _⦋0⦌ :=
  let e := functorEdgeOfSimplicialHomotopy (coherentSpaceTensorProductFstHomotopy F G)
  intervalMappingVertexOfEdge ⟨e.edge, e.src_eq, e.tgt_eq⟩

/-- 第二射影の指定ホモトピーが表す、元の変換空間の頂点。 -/
def coherentSpaceTensorProductSndVertex :
    (leftUnstraighteningTransformationSpace (coherentSpaceTensorProduct F G) G) _⦋0⦌ :=
  let e := functorEdgeOfSimplicialHomotopy (coherentSpaceTensorProductSndHomotopy F G)
  intervalMappingVertexOfEdge ⟨e.edge, e.src_eq, e.tgt_eq⟩

/-- 積図式の小さい全空間から、第一図式の元の小さい全空間への指定作用。 -/
def coherentSpaceTensorProductTotalFst :
    smallLeftUnstraightening (coherentSpaceTensorProduct F G) ⟶ smallLeftUnstraightening F :=
  F2.coherentTransformationTotalMap _ _ (coherentSpaceTensorProductFstVertex F G)

/-- 積図式の小さい全空間から、第二図式の元の小さい全空間への指定作用。 -/
def coherentSpaceTensorProductTotalSnd :
    smallLeftUnstraightening (coherentSpaceTensorProduct F G) ⟶ smallLeftUnstraightening G :=
  F2.coherentTransformationTotalMap _ _ (coherentSpaceTensorProductSndVertex F G)

/-- 同じ二射影を組み合わせた、元の小さい全空間の引き戻しへの比較。 -/
def coherentSpaceTensorProductTotalComparison :
    smallLeftUnstraightening (coherentSpaceTensorProduct F G) ⟶
      pullback (smallLeftUnstraighteningProjection F) (smallLeftUnstraighteningProjection G) :=
  pullback.lift (coherentSpaceTensorProductTotalFst F G) (coherentSpaceTensorProductTotalSnd F G)
    ((F2.coherentTransformationTotalMap_projection _ _ _).trans
      (F2.coherentTransformationTotalMap_projection _ _ _).symm)

/-- 引き戻し比較の第一成分は、指定第一射影の元の全空間作用。 -/
lemma coherentSpaceTensorProductTotalComparison_fst :
    coherentSpaceTensorProductTotalComparison F G ≫ pullback.fst _ _ =
      coherentSpaceTensorProductTotalFst F G := pullback.lift_fst _ _ _

/-- 引き戻し比較の第二成分も、指定第二射影の元の全空間作用。 -/
lemma coherentSpaceTensorProductTotalComparison_snd :
    coherentSpaceTensorProductTotalComparison F G ≫ pullback.snd _ _ =
      coherentSpaceTensorProductTotalSnd F G := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.HomotopyLimits
