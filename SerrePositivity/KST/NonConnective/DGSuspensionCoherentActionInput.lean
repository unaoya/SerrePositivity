module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput
public import SerrePositivity.KST.NonConnective.DGSuspensionEdgeIsoTransport

/-!
概要：全単体作用・元の厳密頂点・端点固定の可逆辺比較による、採用済み B1 利用界面。
方針：辺等号だけを区間写像空間内の指定同型へ緩め、同じ比較を後合成して反復する。
規約：D の正本型だけを使い、構造・ofStrict・辺正規化を複製しない。無条件存在は主張しない。
使われ方：K-7 c4 の互換アダプタ。hF と元の各段の実対象は変更しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.KST.NonConnective
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)

variable (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput R s)

/-- 同じ全単体作用の反復。辺比較の選択を反復対象の定義に使わない。 -/
def DGSuspensionCoherentActionInput.iteration (n : ℕ) :
    dgKInputInfinity.{u, max (u + 1) v} R ⟶ dgKInputInfinity.{u, max (u + 1) v} R :=
  Nat.rec (𝟙 (dgKInputInfinity.{u, max (u + 1) v} R)) (fun _ f => f ≫ a.map) n

/-- B1 でも元の各段の頂点回収は、従来どおりの厳密等号。 -/
theorem DGSuspensionCoherentActionInput.iteration_vertex
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    ((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s a) n).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgSuspensionIteration R s A n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change a.map.app (Opposite.op ⦋0⦌)
      (((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s a) n).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
    rw [ih, a.vertex]
    rfl

/-- 元の各段の厳密頂点に端点を固定した、同じ全反復像の辺。 -/
def DGSuspensionCoherentActionInput.iterationMappedEdge
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (n : ℕ) :
    SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgSuspensionIteration R s A n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgSuspensionIteration R s B n)) :=
  Nat.rec (motive := fun k => SSet.Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgSuspensionIteration R s A k))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgSuspensionIteration R s B k)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)
    (fun k e => (e.map a.map).ofEq
      (a.vertex (dgSuspensionIteration R s A k)) (a.vertex (dgSuspensionIteration R s B k))) n

/-- 再帰的な端点正規化は、同じ全単体反復の辺成分そのものを保持する。 -/
theorem DGSuspensionCoherentActionInput.iterationMappedEdge_edge
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (n : ℕ) :
    ((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iterationMappedEdge R s a) f n).edge =
      ((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s a) n).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change a.map.app (Opposite.op ⦋1⦌) ((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iterationMappedEdge R s a) f n).edge = _
    rw [ih]
    rfl

/-- 同じ全反復像は、元の実反復入力射へ端点固定の指定可逆比較を持つ。 -/
def DGSuspensionCoherentActionInput.iteration_edgeIso
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge ((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iterationMappedEdge R s a) f n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgSuspensionIterationMap R s a.data f n))) := by
  induction n with
  | zero => exact Iso.refl _
  | succ n ih =>
    exact suspensionEdgeIso_post ih a.map
      (a.vertex (dgSuspensionIteration R s A n)) (a.vertex (dgSuspensionIteration R s B n)) ≪≫
        a.edgeIso (dgSuspensionIterationMap R s a.data f n)

end SerrePositivity.InfinityCategories
