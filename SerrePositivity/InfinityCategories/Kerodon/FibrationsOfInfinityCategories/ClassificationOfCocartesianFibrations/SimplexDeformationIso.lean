module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexDeformation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ConstantOrderDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：coherent な単体と最大の区間 path による単体の関手同型。
方針：変形を各頂点で評価すると豊穣恒等に定値であることを計算する。
規約：同型への昇格には coherent nerve の quasicategory 性を仮定する。
使われ方：Kerodon §5.6（Tag 027M）、標準単体上の coherent な表現の局所比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：coherent な単体の変形を各頂点で見ると恒等辺の一単体。
方針：定値の対象写像で変形した path は恒等となり、元の豊穣関手の単位則を使う。
規約：頂点 x は標準単体の任意の頂点。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§5.6（Tag 027M）、単体の変形の点ごとの可逆性。 -/
lemma coherentSimplexDeformation_vertex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) (x : (Δ[n] : SSet.{max u v}) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexDeformation σ) x).edge =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (σ.obj ⟨ULift.up (x.down.toOrderHom 0)⟩)) 1 := by
  obtain ⟨a, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective x
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveVertex_constant]
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  let k : SimplicialThickening (ULift.{u} (Fin (n + 1))) :=
    ⟨ULift.up a⟩
  let t : ULift.{u} (Fin 2) →o Fin 2 :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge.down.toOrderHom.comp ⟨ULift.down, fun _ _ h ↦ h⟩
  change (σ.map k k).app d
      ((nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationFunctor
        (OrderHom.const (ULift.{u} (Fin 2)) k.as)
        t i.as j.as)).app d P) =
    (eId SSet (σ.obj k)).app d PUnit.unit
  have hP : (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformationFunctor
        (OrderHom.const (ULift.{u} (Fin 2)) k.as)
        t i.as j.as)).app d P =
      (eId SSet k).app d PUnit.unit := by
    apply CategoryTheory.Functor.ext (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPathDeformation_constant k.as _ (P.obj z))
  rw [hP]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (σ.map_id k) d) PUnit.unit

/-- 概要：coherent な単体の最大化への変形は全ての頂点で可逆。
方針：各頂点の辺は恒等の一単体と等しいので、そのホモトピー圏の射は同型。
規約：この判定には局所 Kan 性は不要。
使われ方：Kerodon §4.5.1（Tag 01DQ）、§5.6（Tag 027M）、局所比較を関手同型へ昇格する。 -/
lemma coherentSimplexDeformation_vertex_isInvertible
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) (x : (Δ[n] : SSet.{max u v}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexDeformation σ) x).toTruncated := by
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexDeformation σ) x).toTruncated.edge =
      (SSet.Truncated.Edge.id (X := (truncation 2).obj (SimplicialNerve C))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (σ.obj ⟨ULift.up (x.down.toOrderHom 0)⟩))).edge :=
    (coherentSimplexDeformation_vertex σ x).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr h).mpr
  change IsIso (SSet.Truncated.HomotopyCategory.homMk
    (SSet.Truncated.Edge.id (X := (truncation 2).obj (SimplicialNerve C))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (σ.obj ⟨ULift.up (x.down.toOrderHom 0)⟩))))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

/-- 概要：coherent な単体と最大の区間 path のみを使う単体は関手同型。
方針：構成したホモトピーの各頂点での可逆性を点ごとの同型の判定へ適用する。
規約：標的の coherent nerve が quasicategory であることだけを追加する。
使われ方：Kerodon §5.6（Tag 027M）、標準単体上の coherent な図式と strict な射列を比較する。 -/
noncomputable def coherentSimplexMaximalizationIso
    {C : Type v} [Category.{u} C] [SimplicialCategory C] [Quasicategory (SimplicialNerve C)]
    {n : ℕ} (σ : (SimplicialNerve C) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (SSet.yonedaEquiv.symm σ)
      (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexMaximalization σ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentSimplexDeformation σ)
    (coherentSimplexDeformation_vertex_isInvertible σ)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
