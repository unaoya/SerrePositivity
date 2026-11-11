module
public import SerrePositivity.KST.NonConnective.DGSuspensionIterationMaps

/-!
概要：選んだ同じ cone による懸垂を、固定 dg 提示源の全単体へ作用させる明示供給境界。
方針：PerfDGInput 上の厳密 SSet 豊穣自己関手の coherentNerveMap を供給路とし、元の頂点・辺を照合する。
規約：採用（03:55）の独立した明示入力。I・P の対象別供給や通常射の恒等・合成から存在を推論しない。
使われ方：K-7 c4。供給された場合の全高次反復と元の段別入力の条件付き照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)

/-- 採用（03:55）：同じ対象別供給を保つ、固定 S 上の全高次懸垂作用の明示入力。 -/
structure DGSuspensionNativeActionInput where
  /-- K-B の全高次作用。D-8 の対象別 I・P だけでは供給済みと数えない。 -/
  map : dgKInputInfinity.{u, max (u + 1) v} R ⟶ dgKInputInfinity.{u, max (u + 1) v} R
  /-- 同じ選択 cone の元の実平坦商を頂点で保持する。 -/
  vertex : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
    map.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R A (s A).cone)
  /-- 各元の厳密 dg 射に対する、同じ cone・平坦分解の実作用。 -/
  data : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R}, (A ⟶ B) →
    DGKappaSuspensionMapData R A B (s A).cone (s B).cone
  /-- 全高次作用の元の一単体は、同じ実商関手の一単体そのもの。 -/
  edge : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B),
    map.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKappaSuspensionInputMap R A B (s A).cone (s B).cone (data f))).edge

variable (a : DGSuspensionNativeActionInput R s)

/-- 明示された全高次作用に条件付きの、同じ固定 S 上の反復作用。 -/
def DGSuspensionNativeActionInput.iteration (n : ℕ) :
    dgKInputInfinity.{u, max (u + 1) v} R ⟶ dgKInputInfinity.{u, max (u + 1) v} R :=
  Nat.rec (𝟙 _) (fun _ f => f ≫ a.map) n

/-- 明示全高次作用に条件付きで、その反復の頂点は既存の同じ段別実平坦商である。 -/
theorem DGSuspensionNativeActionInput.iteration_vertex
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    (DGSuspensionNativeActionInput.iteration R s a n).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgSuspensionIteration R s A n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change a.map.app (Opposite.op ⦋0⦌)
      ((DGSuspensionNativeActionInput.iteration R s a n).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
    rw [ih, a.vertex]
    rfl

/-- 明示全高次作用に条件付きで、元の厳密 dg 辺の全反復像は同じ実懸垂入力射の辺。 -/
theorem DGSuspensionNativeActionInput.iteration_edge
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (n : ℕ) :
    (DGSuspensionNativeActionInput.iteration R s a n).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgSuspensionIterationMap R s a.data f n)).edge := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change a.map.app (Opposite.op ⦋1⦌)
      ((DGSuspensionNativeActionInput.iteration R s a n).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).edge) = _
    rw [ih, a.edge]
    rfl

end SerrePositivity.KST.NonConnective
