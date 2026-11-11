module
public import SerrePositivity.KST.NonConnective.DGSuspensionCoherentActionInput
public import SerrePositivity.KST.NonConnective.DGSuspensionNativeStageFamily

/-!
概要：採用 B1 の全反復作用を、元の各段の固定 K・native loop へ送る。
方針：元の厳密頂点を保持し、端点固定比較を同じ K と loop で後合成する。
規約：辺比較を厳密等号へ戻さない。元の hF や構造辺 β の自然性は別工程。
使われ方：K-7 c4 の StageFamily_edge の可逆比較版。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance coherentStageSpectrumCategory : SimplicialCategory OmegaSpectrum.{w} :=
  OmegaSpectrum.simplicialCategory
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ) (a : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput R s)

/-- 同じ全反復・固定 K・同じ native loop による全入力段族。 -/
def dgSuspensionCoherentStageFamily (n : ℕ) :
    dgKInputInfinity.{u, max (u + 1) v} R ⟶ Sp.{max (u + 1) v} :=
  (_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s a) n ≫ dgKInputK R ≫ (End.of OmegaSpectrum.nativeLoop ^ n).asHom

/-- 各段の頂点は、従来どおり元の同じ実 BF 列の頂点に厳密一致する。 -/
theorem dgSuspensionCoherentStageFamily_vertex
    (A : PerfDGInput.{u, max (u + 1) v} R) (n : ℕ) :
    (dgSuspensionCoherentStageFamily R s a n).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A) = dgSuspensionNativeSequenceVertex R s A n := by
  change ((End.of OmegaSpectrum.nativeLoop ^ n).asHom).app (Opposite.op ⦋0⦌)
    ((dgKInputK R).app (Opposite.op ⦋0⦌)
      (((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration R s a) n).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex A))) = _
  rw [DGSuspensionCoherentActionInput.iteration_vertex, dgKInputK_vertex]
  rfl

/-- 元の厳密反復 dg 入力射を K と同じ回数の loop へ送った指定辺。 -/
def dgSuspensionCoherentStageInputEdge
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (n : ℕ) :
    Sp.Edge (dgSuspensionNativeSequenceVertex R s A n) (dgSuspensionNativeSequenceVertex R s B n) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKInputSpectrumMap R
    (dgSuspensionIterationMap R s a.data f n))).map (End.of OmegaSpectrum.nativeLoop ^ n).asHom

/-- 元の全段族の辺を、同じ厳密頂点で正規化する。 -/
def dgSuspensionCoherentStageMappedEdge
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (n : ℕ) :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).map (dgSuspensionCoherentStageFamily R s a n)).ofEq
    (dgSuspensionCoherentStageFamily_vertex R s a A n)
    (dgSuspensionCoherentStageFamily_vertex R s a B n)

/-- 同じ段族の全辺は、元の反復 BF 射の loop 像へ端点固定の指定可逆比較を持つ。 -/
def dgSuspensionCoherentStageFamily_edgeIso
    {A B : PerfDGInput.{u, max (u + 1) v} R} (f : A ⟶ B) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (dgSuspensionCoherentStageMappedEdge R s a f n))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (dgSuspensionCoherentStageInputEdge R s a f n)) := by
  let fₙ := dgSuspensionIterationMap R s a.data f n
  let eₙ := (_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iterationMappedEdge R s a) f n
  have eK := suspensionEdgeIso_post ((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iteration_edgeIso R s a) f n) (dgKInputK R)
    (dgKInputK_vertex R (dgSuspensionIteration R s A n))
    (dgKInputK_vertex R (dgSuspensionIteration R s B n))
  have eK' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge ((eₙ.map (dgKInputK R)).ofEq
        (dgKInputK_vertex R (dgSuspensionIteration R s A n))
        (dgKInputK_vertex R (dgSuspensionIteration R s B n))))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingVertexOfEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgKInputSpectrumMap R fₙ))) :=
    suspensionEdgeIso_ofEdgeComponents eK rfl (dgKInputK_edge R fₙ)
  let L := (End.of OmegaSpectrum.nativeLoop ^ n).asHom
  have eL := suspensionEdgeIso_post eK' L rfl rfl
  have h₀ : ((((eₙ.map (dgKInputK R)).ofEq
        (dgKInputK_vertex R (dgSuspensionIteration R s A n))
        (dgKInputK_vertex R (dgSuspensionIteration R s B n))).map L).ofEq rfl rfl).edge =
      (dgSuspensionCoherentStageMappedEdge R s a f n).edge :=
    congrArg (fun x => L.app (Opposite.op ⦋1⦌) ((dgKInputK R).app (Opposite.op ⦋1⦌) x))
      ((_root_.SerrePositivity.InfinityCategories.DGSuspensionCoherentActionInput.iterationMappedEdge_edge R s a) f n)
  exact suspensionEdgeIso_ofEdgeComponents eL h₀ rfl

/-- 旧厳密作用の段族を、新しい比較入口でも同じ全単体の射として保持する。 -/
theorem dgSuspensionCoherentStageFamily_ofStrict
    (b : DGSuspensionNativeActionInput R s) (n : ℕ) :
    dgSuspensionCoherentStageFamily R s (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSuspensionCoherentActionInput.ofStrict R s b) n =
      dgSuspensionNativeStageFamily R s b n := rfl

end SerrePositivity.KST.NonConnective
