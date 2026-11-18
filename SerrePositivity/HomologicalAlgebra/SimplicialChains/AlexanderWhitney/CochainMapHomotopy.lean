module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainDiagonal
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-!
# 単体的ホモトピーから元の正規化コチェイン射のホモトピーへ

概要：単体集合の実円柱から同じ正規化射の鎖ホモトピーを構成する。
方針：自由加群化した交代面複体のホモトピーを Moore 包含・射影で挟んで延長する。
規約：同じ normalizedFunctor と元の射を保持し、モデル構造を入力しない。
使われ方：標準ホーンの実収縮と元の包含射の擬同型性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.SimplicialChains.AlexanderWhitney
open _root_.CategoryTheory _root_.AlgebraicTopology _root_.AlgebraicTopology.DoldKan
variable (A : Type u) [CommRing A]

/-- 概要：正規化鎖写像は交代面写像を Moore 包含・射影で挟んだもの。
方針：射影の自然性と分裂単射の恒等式を使う。規約：元の射自身の等式。
使われ方：正規化前のホモトピーの端点を回収する。 -/
lemma normalizedChainMap_conjugate {X Y : SSet.{0}} (f : X ⟶ Y) :
    inclusionOfMooreComplexMap ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X) ≫
      (alternatingFaceMapComplex (ModuleCat A)).map ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f) ≫
      PInftyToNormalizedMooreComplex ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Y) =
      (normalizedMooreComplex (ModuleCat A)).map ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f) := by
  change inclusionOfMooreComplexMap _ ≫ AlternatingFaceMapComplex.map _ ≫
    PInftyToNormalizedMooreComplex _ = NormalizedMooreComplex.map _
  rw [PInftyToNormalizedMooreComplex_naturality, ← Category.assoc]
  erw [(splitMonoInclusionOfMooreComplexMap ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X)).id,
    Category.id_comp]

/-- 概要：単体的な実ホモトピーは元の cochainMap の鎖ホモトピーを与える。
方針：交代面複体のホモトピーを包含と射影で挟み、負次数へ延長する。
規約：任意可換環と小さい単体集合。正規化射の端点を変えない。
使われ方：ホーン内の二つの円柱から収縮ホモトピーを作る。 -/
def cochainMapHomotopy {X Y : SSet.{0}} {f g : X ⟶ Y} (H : SSet.Homotopy f g) :
    Homotopy (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A f) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A g) := by
  let h : Homotopy
      ((alternatingFaceMapComplex (ModuleCat A)).map ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f))
      ((alternatingFaceMapComplex (ModuleCat A)).map ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map g)) :=
    (H.toSimplicialObjectHomotopy.whiskerRight
      (uliftFunctor.{u, 0} ⋙ ModuleCat.free A)).toChainHomotopy
  let h' :=
    (h.compLeft (inclusionOfMooreComplexMap ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj X))).compRight
    (PInftyToNormalizedMooreComplex ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).obj Y))
  have h'' : Homotopy
      ((normalizedMooreComplex (ModuleCat A)).map ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map f))
      ((normalizedMooreComplex (ModuleCat A)).map ((_root_.SerrePositivity.EInfinity.BarrattEccles.linearization A).map g)) := by
    simpa only [Category.assoc, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.normalizedChainMap_conjugate] using h'
  exact h''.extend ComplexShape.embeddingDownNat

end SerrePositivity.SimplicialChains.AlexanderWhitney
