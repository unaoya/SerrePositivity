module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointIteratedLoops

/-!
概要：自明 Kan 射影を実 loop 全図式へ送り、同じ全図式射影の境界 RLP を認証する。
方針：周囲の全関手空間で持ち上げ、同じ射影の下の loop 性反映で全部分圏へ戻す。
規約：全 Hom・全単体を保ち、安定性は仮定しない。使われ方：反復実図式の比較一意性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

section
variable {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (q : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration q]

/-- 同じ自明 Kan 射影による全四角形の像を、元の実 loop 全図式へ制限する。 -/
def d3LoopDiagramTrivialImage : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams E ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map q)
    (by
      intro v
      apply (d3IsLoopDiagramVertex_iff_trivialKan_image q _).mp
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v)

lemma d3LoopDiagramTrivialImage_ι :
    d3LoopDiagramTrivialImage q ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map q :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 同じ射影の全四角形像は、全ての角評価と厳密に交換する。 -/
lemma d3LoopDiagramTrivialImage_corner (i j : Fin 2) :
    d3LoopDiagramTrivialImage q ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation B i j =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation E i j ≫ q := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation]
  rw [← Category.assoc, d3LoopDiagramTrivialImage_ι, Category.assoc,
    OmegaSpectrum.AdjointLoopRelativeBF.d3SquareEvaluation_postcomp]
  exact (Category.assoc _ _ _).symm

/-- 全図式射影の境界充填は、実 loop 部分圏でも元の全パラメータを保って持ち上がる。 -/
instance d3LoopDiagramTrivialImage_trivial : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (d3LoopDiagramTrivialImage q) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).mpr
  intro n
  constructor
  intro a b sq
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem
    (p := (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map q) (boundary n).ι inferInstance
  let sq' : CommSq (a ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι)
      (boundary n).ι ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map q)
      (b ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι) := ⟨by
    rw [Category.assoc, ← d3LoopDiagramTrivialImage_ι, ← Category.assoc,
      sq.w, Category.assoc]⟩
  have hl (v : (Δ[n] : SSet.{u + 1}) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex (sq'.lift.app _ v) := by
    apply (d3IsLoopDiagramVertex_iff_trivialKan_image q _).mpr
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex ((sq'.lift ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map q).app _ v)
    rw [sq'.fac_right]
    simpa only [NatTrans.comp_app, Subfunctor.ι, types_comp_apply, TypeCat.ofHom_apply] using
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (b.app _ v))
  refine CommSq.HasLift.mk' {
    l := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex sq'.lift hl
    fac_left := ?_
    fac_right := ?_ }
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
    exact sq'.fac_left
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsLoopDiagramVertex).ι).mp
    rw [Category.assoc, d3LoopDiagramTrivialImage_ι, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι]
    exact sq'.fac_right
end

end SerrePositivity.KST.Spectra
