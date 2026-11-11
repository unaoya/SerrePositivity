module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：可逆な path の単体集合の射に関する関手性。
方針：区間からの内部 Hom の後合成を、可逆な辺を選ぶ全部分複体に制限する。
規約：元の単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.5.5（Tag 01F6） の同値な図式の貼り合わせ。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：区間関手の頂点が表す辺は後合成と可換。
方針：頂点を区間からの射で表し、Yoneda 同値を計算する。
規約：任意の単体集合の射。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆な path の関手性。 -/
lemma intervalFunctorVertexEdge_map {X Y : SSet.{u}} (f : X ⟶ Y)
    (v : ((ihom (Δ[1] : SSet.{u})).obj X) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((ihom (Δ[1] : SSet.{u})).map f).app (Opposite.op ⦋0⦌) v) =
      f.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge v) := by
  obtain ⟨h, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[1] X).surjective v
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (h ≫ f)) =
    f.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex,
    SSet.yonedaEquiv_comp]

/-- 概要：単体集合の射は可逆な path の単体集合の射を誘導する。
方針：区間の内部 Hom の後合成が可逆な辺を保つことを使う。
規約：標的と始域の quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.5.5（Tag 01F6） の path の比較。 -/
def equivalencePathMap {X Y : SSet.{u}} (f : X ⟶ Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X ≫ (ihom (Δ[1] : SSet.{u})).map f) (fun v ↦ by
      have hv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex v.val at hv
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
        (((ihom (Δ[1] : SSet.{u})).map f).app (Opposite.op ⦋0⦌) v.val)
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex at hv ⊢
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (intervalFunctorVertexEdge_map f v.val)).mpr (hv.map f))

/-- 概要：可逆な path の射を内部 Hom に含めると元の後合成になる。
方針：全部分複体への持ち上げの計算を使う。
規約：任意の単体集合の射。
使われ方：Kerodon §4.5.3（Tag 032Y） の端点と射の比較。 -/
lemma equivalencePathMap_ι {X Y : SSet.{u}} (f : X ⟶ Y) :
    equivalencePathMap f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X ≫ (ihom (Δ[1] : SSet.{u})).map f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：可逆な path の射は両端の評価と可換。
方針：後合成と評価の順序を各次数で計算する。
規約：i は Fin 2 のいずれの端点でもよい。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.5.5（Tag 01F6） の相対 path。 -/
lemma equivalencePathMap_endpoint {X Y : SSet.{u}} (f : X ⟶ Y) (i : Fin 2) :
    equivalencePathMap f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Y i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X i ≫ f := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro v
  rfl

/-- 概要：可逆な path の恒等射からの誘導射は恒等。
方針：内部 Hom の後合成の恒等式を全部分複体の包含で検査する。
規約：任意の単体集合 X。
使われ方：Kerodon §4.5.3（Tag 032Y） の path の関手性。 -/
lemma equivalencePathMap_id (X : SSet.{u}) : equivalencePathMap (𝟙 X) = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι; infer_instance
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)).1
  rw [equivalencePathMap_ι, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp]

/-- 概要：可逆な path の誘導射は合成を保つ。
方針：内部 Hom の後合成の合成則を包含で検査する。
規約：元の射と同じ順序で合成する。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.5.5（Tag 01F6） の path の図式。 -/
lemma equivalencePathMap_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    equivalencePathMap (f ≫ g) = equivalencePathMap f ≫ equivalencePathMap g := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Z) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι; infer_instance
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι Z)).1
  rw [equivalencePathMap_ι, Category.assoc, equivalencePathMap_ι,
    ← Category.assoc, equivalencePathMap_ι, CategoryTheory.Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
