module
public import SerrePositivity.KST.NonConnective.DGSuspensionCoherentStageFamily
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeSquareFamily
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FibrantModels.DGSuspensionCoherentSquareInput

/-!
概要：元の厳密 hF を保つ全四角形族を、採用 B1 の反復作用へ接続する。
方針：懸垂角の厳密頂点は既存の照合を使い、hedge だけを端点固定可逆比較へ置換する。
規約：元の全族・実四角形・全四角形等号を変更しない。供給の存在は別工程。
使われ方：K-7 c4 の ofSquareFamily と全反復四角形の互換入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R]
  (F : ((Δ[1] ⊗ Δ[1]) ⊗ dgKInputInfinity.{u, max (u + 1) v} R) ⟶
    dgKInputInfinity.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (s : DGSuspensionStageProvider.{u, v} R κ)
  (hF : ∀ A : PerfDGInput.{u, max (u + 1) v} R,
    dgSuspensionNativeSquareAt R F A = dgKappaResolvedConnectiveSquare R A (s A).cone)

include hF in
/-- 元の厳密 hF からの懸垂角の頂点照合は、既存の式をそのまま使う。 -/
theorem dgSuspensionCoherentSquareSuspension_vertex
    (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgSuspensionNativeSquareCornerFamily R F 1 1).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgKappaSuspensionKInput R A (s A).cone) :=
  (dgSuspensionNativeSquareCornerFamily_at R F s hF 1 1 A).trans
    (dgKappaResolvedConnectiveSquare_vertices R A (s A).cone).2.2.1

/-- 元の厳密 hF を保持し、hedge を端点固定の指定可逆比較にした全作用入口。 -/
def _root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.ofSquareFamily
    (d : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R}, (A ⟶ B) →
      DGKappaSuspensionMapData R A B (s A).cone (s B).cone)
    (hedgeIso : ∀ {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSuspensionMappedEdge R s
        (dgSuspensionNativeSquareCornerFamily R F 1 1)
        (dgSuspensionCoherentSquareSuspension_vertex R F s hF) f))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (dgKappaSuspensionInputMap R A B (s A).cone (s B).cone (d f))))) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput R s where
  map := dgSuspensionNativeSquareCornerFamily R F 1 1
  vertex := dgSuspensionCoherentSquareSuspension_vertex R F s hF
  data := d
  edgeIso := hedgeIso

variable (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput R s)

/-- 同じ全四角形族を、B1 の同じ全作用で反復する。 -/
def dgSuspensionCoherentSquareIterationFamily (n : ℕ) :=
  (_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s a) n ≫ dgSuspensionNativeSquareDiagramFamily R F

/-- 反復後の全単体も、元の同じ全四角形族を厳密回収する。 -/
theorem dgSuspensionCoherentSquareIterationFamily_recovery (n : ℕ) :
    uncurry (dgSuspensionCoherentSquareIterationFamily R F s a n) =
      (Δ[1] ⊗ Δ[1]) ◁ (_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s a) n ≫ F := by
  rw [dgSuspensionCoherentSquareIterationFamily, uncurry_natural_left,
    dgSuspensionNativeSquareDiagramFamily_recovery]

include hF in
/-- B1 の反復でも、各入力の元の全四角形への厳密 hF 照合は保持する。 -/
theorem dgSuspensionCoherentSquareIterationFamily_at
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    (dgSuspensionCoherentSquareIterationFamily R F s a n).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgKappaResolvedConnectiveSquare R
        (dgSuspensionIteration R s A n) (dgSuspensionIterationStage R s A n).cone) := by
  change (dgSuspensionNativeSquareDiagramFamily R F).app (Opposite.op ⦋0⦌)
    (((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s a) n).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
  rw [DGSuspensionCoherentActionInput.iteration_vertex]
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgSuspensionNativeSquareAt R F (dgSuspensionIteration R s A n)) =
      (dgSuspensionNativeSquareDiagramFamily R F).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (dgSuspensionIteration R s A n)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply _
  rw [← hv, hF]
  rfl

include hF in
/-- 元の全反復四角形の固定 K 像も、従来の厳密 hF による照合を保持する。 -/
theorem dgSuspensionCoherentKSquareIterationFamily_at
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    ((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s a) n ≫ dgSuspensionNativeKSquareFamily R F).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgKappaResolvedConnectiveSquare R
        (dgSuspensionIteration R s A n) (dgSuspensionIterationStage R s A n).cone ≫
          dgKInputK R) := by
  change (dgSuspensionNativeKSquareFamily R F).app (Opposite.op ⦋0⦌)
    (((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s a) n).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A)) = _
  rw [DGSuspensionCoherentActionInput.iteration_vertex]
  exact dgSuspensionNativeKSquareFamily_at R F s hF (dgSuspensionIteration R s A n)

variable (p : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentSquareInput R s)

/-- D 正本の同じ四角形・同じ作用を、複製や選び直しなしで反復利用する。 -/
def dgSuspensionCoherentSuppliedSquareIterationFamily (n : ℕ) :=
  dgSuspensionCoherentSquareIterationFamily R p.square s p.action n

/-- D 正本の厳密 hF を直接消費して、同じ各段の全四角形を回収する。 -/
theorem dgSuspensionCoherentSuppliedSquareIterationFamily_at
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    (dgSuspensionCoherentSuppliedSquareIterationFamily R s p n).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (dgKappaResolvedConnectiveSquare R
        (dgSuspensionIteration R s A n) (dgSuspensionIterationStage R s A n).cone) :=
  dgSuspensionCoherentSquareIterationFamily_at R p.square s p.square_at p.action A n

/-- D 正本の同じ懸垂角の全単体作用は、同じ action.map に厳密一致する。 -/
theorem dgSuspensionCoherentSuppliedSquare_suspension :
    dgSuspensionNativeSquareCornerFamily R p.square 1 1 = p.action.map :=
  p.suspension

end SerrePositivity.KST.NonConnective
