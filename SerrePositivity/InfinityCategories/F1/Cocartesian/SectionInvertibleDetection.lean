module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionsRestrictionLifting
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FullSubcomplexFunctorFaithful
public import SerrePositivity.InfinityCategories.Core.VertexFiberInvertible
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-!
概要：cocartesian section 間の変換の可逆性を、元の全空間内の点ごとの成分で検出する。
方針：全部分複体の包含と相対 fiber の包含で可逆性を反映し、内部 Hom の評価で判定する。
規約：始域の単体集合の quasicategory 性を要求しない。
使われ方：section の core の所属条件をセルの貼り合わせで検出する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 内部 Hom の任意の端点を持つ辺の可逆性は、全ての頂点での評価で検出できる。 -/
lemma isInvertibleEdge_internalHom_iff_evaluate {A E : SSet.{u}} [Quasicategory E]
    {v w : ((ihom A).obj E) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom A).obj E)) v w) :
    IsInvertibleEdge e ↔ ∀ x : A _⦋0⦌,
      IsInvertibleEdge (e.map ((truncation 2).map (evaluateFunctorAt (Y := E) x))) := by
  obtain ⟨f, rfl⟩ := (functorVertexEquiv A E).surjective v
  obtain ⟨g, rfl⟩ := (functorVertexEquiv A E).surjective w
  exact isInvertibleEdge_iff_evaluateFunctorAt e

/-- section の元の関手を、指定した始域の頂点で評価する。 -/
def cocartesianSectionEvaluate {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (x : A _⦋0⦌) : SerrePositivity.InfinityCategories.cocartesianSections p a ⟶ E :=
  SerrePositivity.InfinityCategories.cocartesianSectionsι p a ≫
    vertexFiberι ((ihom A).map p) (functorVertex a) ≫ evaluateFunctorAt x

/-- section の辺は、全ての元の頂点で評価した成分が可逆のとき、かつそのときに限り可逆。 -/
lemma isInvertibleEdge_cocartesianSection_iff_evaluate {A E B : SSet.{u}}
    [Quasicategory B] (p : E ⟶ B) [InnerFibration p] (a : A ⟶ B)
    {v w : (SerrePositivity.InfinityCategories.cocartesianSections p a) _⦋0⦌}
    (e : Truncated.Edge (X := (truncation 2).obj (SerrePositivity.InfinityCategories.cocartesianSections p a)) v w) :
    IsInvertibleEdge e ↔ ∀ x : A _⦋0⦌,
      IsInvertibleEdge (e.map ((truncation 2).map (cocartesianSectionEvaluate p a x))) := by
  let : Quasicategory E := quasicategory_of_innerFibration p
  let : Quasicategory (SerrePositivity.InfinityCategories.relativeFunctorSpace p a) :=
    inferInstanceAs (Quasicategory (relativeFunctorSpace p a))
  constructor
  · intro he x
    exact he.map _
  · intro he
    apply (isFullyFaithful_fullSubcomplexOnVertices_ι
      (SerrePositivity.InfinityCategories.relativeFunctorSpace p a) (SerrePositivity.InfinityCategories.IsCocartesianSection p
        a)).reflects_isInvertibleEdge e
    apply (isInvertibleEdge_vertexFiber_iff ((ihom A).map p) (functorVertex a) _).mpr
    apply (isInvertibleEdge_internalHom_iff_evaluate _).mpr
    exact he

end SerrePositivity.InfinityCategories
