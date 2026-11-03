module

public import SerrePositivity.KST.Spectra.D3LoopCanonicalSectionTransport
public import SerrePositivity.InfinityCategories.Stable.SquareTransposeEvaluation
public import SerrePositivity.InfinityCategories.F1.SquareDuality

/-!
概要：実 loop 図式の二つの零角の交換を、全 Hom・全単体を持つ転置作用にする。
方針：全四角形の前合成を loop 図式の全部分圏へ制限し、各角と二回合成を計算する。
規約：円交換因子を比較しない。loop 図式の対角頂点は厳密に保持する。
使われ方：保持した模型補正を扱うための、実図式に由来する反転作用の構成。
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

lemma d3SquareDiagram_pre_transpose {X : SSet.{u}}
    (v : ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) _⦋0⦌) :
    squareDiagram (((pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app X).app _ v) =
      (β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ squareDiagram v := by
  obtain ⟨F, rfl⟩ := (functorVertexEquiv ((Δ[1] : SSet.{u}) ⊗ Δ[1]) X).surjective v
  change squareDiagram (functorVertex ((β_ _ _).hom ≫ F)) =
    (β_ _ _).hom ≫ squareDiagram (functorVertex F)
  rw [squareDiagram_functorVertex, squareDiagram_functorVertex]

/-- 元の全四角形の転置は、零角と引き戻し性を同時に保つ。 -/
lemma d3IsLoopDiagramVertex_transpose {X : SSet.{u}}
    (v : ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) _⦋0⦌)
    (hv : IsLoopDiagramVertex v) :
    IsLoopDiagramVertex (((pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app X).app _ v) := by
  dsimp only [IsLoopDiagramVertex] at hv ⊢
  rw [d3SquareDiagram_pre_transpose]
  exact ⟨hv.2.1, hv.1, (isPullbackSquare_iff_transpose _).mp hv.2.2⟩

/-- 二つの零角を交換する、実 loop 全図式上の全単体作用。 -/
def d3LoopDiagramTranspose (X : SSet.{u}) : loopDiagrams X ⟶ loopDiagrams X :=
  fullSubcomplexLift (A := loopDiagrams X)
    (X := (ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) IsLoopDiagramVertex
    ((fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X)
      IsLoopDiagramVertex).ι ≫
      (pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app X)
    (by
      intro v
      change IsLoopDiagramVertex
        (((pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app X).app _ v.val)
      exact d3IsLoopDiagramVertex_transpose (X := X) v.val
        (fullSubcomplexOnVertices_vertex v))

lemma d3LoopDiagramTranspose_ι (X : SSet.{u}) :
    d3LoopDiagramTranspose X ≫ (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι =
      (fullSubcomplexOnVertices _ IsLoopDiagramVertex).ι ≫
        (pre (β_ (Δ[1] : SSet.{u}) Δ[1]).hom).app X := fullSubcomplexLift_ι _ _ _

/-- 転置の各角の作用は、元の同じ角の交換に厳密一致。 -/
lemma d3LoopDiagramTranspose_corner (X : SSet.{u}) (i j : Fin 2) :
    d3LoopDiagramTranspose X ≫ loopDiagramEvaluation X i j =
      loopDiagramEvaluation X j i := by
  dsimp only [loopDiagramEvaluation]
  rw [← Category.assoc, d3LoopDiagramTranspose_ι, Category.assoc,
    stable_pre_evaluateFunctorAt]
  rfl

/-- 実 loop 全図式の二回の転置は、全単体で元の恒等作用。 -/
lemma d3LoopDiagramTranspose_comp_self (X : SSet.{u}) :
    d3LoopDiagramTranspose X ≫ d3LoopDiagramTranspose X = 𝟙 _ := by
  let ι := (fullSubcomplexOnVertices
    ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) IsLoopDiagramVertex).ι
  apply (cancel_mono ι).mp
  dsimp only [ι]
  rw [Category.assoc, d3LoopDiagramTranspose_ι, ← Category.assoc,
    d3LoopDiagramTranspose_ι, Category.assoc]
  rw [← NatTrans.comp_app, ← pre_map, SymmetricCategory.symmetry, pre_id]
  simp only [NatTrans.id_app, Category.comp_id, Category.id_comp]

end SerrePositivity.KST.Spectra
