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
    (q : E ⟶ B) [TrivialKanFibration q]

/-- 同じ自明 Kan 射影による全四角形の像を、元の実 loop 全図式へ制限する。 -/
def d3LoopDiagramTrivialImage : loopDiagrams E ⟶ loopDiagrams B :=
  fullSubcomplexLift IsLoopDiagramVertex
    ((fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map q)
    (by
      intro v
      apply (d3IsLoopDiagramVertex_iff_trivialKan_image q _).mp
      exact fullSubcomplexOnVertices_vertex v)

lemma d3LoopDiagramTrivialImage_ι :
    d3LoopDiagramTrivialImage q ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι =
    (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map q :=
  fullSubcomplexLift_ι _ _ _

/-- 同じ射影の全四角形像は、全ての角評価と厳密に交換する。 -/
lemma d3LoopDiagramTrivialImage_corner (i j : Fin 2) :
    d3LoopDiagramTrivialImage q ≫ loopDiagramEvaluation B i j =
      loopDiagramEvaluation E i j ≫ q := by
  dsimp only [loopDiagramEvaluation]
  rw [← Category.assoc, d3LoopDiagramTrivialImage_ι, Category.assoc,
    OmegaSpectrum.AdjointLoopRelativeBF.d3SquareEvaluation_postcomp]
  exact (Category.assoc _ _ _).symm

/-- 全図式射影の境界充填は、実 loop 部分圏でも元の全パラメータを保って持ち上がる。 -/
instance d3LoopDiagramTrivialImage_trivial : TrivialKanFibration (d3LoopDiagramTrivialImage q) := by
  apply (trivialKanFibration_iff_boundary _).mpr
  intro n
  constructor
  intro a b sq
  have := TrivialKanFibration.mem
    (p := (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map q) (boundary n).ι inferInstance
  let sq' : CommSq (a ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι)
      (boundary n).ι ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map q)
      (b ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι) := ⟨by
    rw [Category.assoc, ← d3LoopDiagramTrivialImage_ι, ← Category.assoc,
      sq.w, Category.assoc]⟩
  have hl (v : (Δ[n] : SSet.{u + 1}) _⦋0⦌) :
      IsLoopDiagramVertex (sq'.lift.app _ v) := by
    apply (d3IsLoopDiagramVertex_iff_trivialKan_image q _).mpr
    change IsLoopDiagramVertex ((sq'.lift ≫
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map q).app _ v)
    rw [sq'.fac_right]
    simpa only [NatTrans.comp_app, Subfunctor.ι, types_comp_apply, TypeCat.ofHom_apply] using
      (fullSubcomplexOnVertices_vertex (b.app _ v))
  refine CommSq.HasLift.mk' {
    l := fullSubcomplexLift IsLoopDiagramVertex sq'.lift hl
    fac_left := ?_
    fac_right := ?_ }
  · apply (cancel_mono (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι).mp
    rw [Category.assoc, fullSubcomplexLift_ι]
    exact sq'.fac_left
  · apply (cancel_mono (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι).mp
    rw [Category.assoc, d3LoopDiagramTrivialImage_ι, ← Category.assoc,
      fullSubcomplexLift_ι]
    exact sq'.fac_right
end

end SerrePositivity.KST.Spectra
