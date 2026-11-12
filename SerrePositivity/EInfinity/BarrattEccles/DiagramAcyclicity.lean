module

public import SerrePositivity.EInfinity.BarrattEccles.ModelCategory
public import SerrePositivity.EInfinity.Operad.AlgebraDiagramSmallness
public import SerrePositivity.HomotopicalAlgebra.Transfer.CellMap

/-!
# 小さい E 代数図式の生成 trivial cofibration の非循環性

概要：BM 命題 4.1 の具体的な E 代数モデルから図式の J-cell 非循環性を得る。
方針：自由図式の各成分は trivial cofibration の余積で、評価は余極限を保つ。
規約：任意の小圏、図式の始域の cofibrancy は不要。
使われ方：一般図式の射影モデルと導来忘却の構成。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.BarrattEccles.Diagram

open CategoryTheory Limits HomotopicalAlgebra
open Operad.AlgebraDiagram

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

/-- 概要：図式モデルの生成 cofibration のクラス（BM 命題 4.1）。
方針：複体の生成射を自由代数と全頂点の自由図式へ移す。
規約：自由像そのものの合併を使う。
使われ方：図式の第一の小対象分解。 -/
abbrev generatingCofibrations : MorphismProperty (K ⥤ (operad A).Algebra) :=
  generators (operad A) K
    ((projectiveGeneratingCofibrations A).strictMap (operad A).freeAlgebraFunctor)

/-- 概要：図式モデルの生成 trivial cofibration のクラス（BM 命題 4.1）。
方針：零から disk への射を自由代数と各頂点の自由図式へ移す。
規約：図式は任意の小圏上の通常の関手。
使われ方：図式の第二の小対象分解と非循環性。 -/
abbrev generatingTrivialCofibrations : MorphismProperty (K ⥤ (operad A).Algebra) :=
  generators (operad A) K
    ((projectiveGeneratingTrivialCofibrations A).strictMap (operad A).freeAlgebraFunctor)

set_option synthInstance.maxHeartbeats 40000 in
/-- 概要：自由図式の生成 trivial cofibration は全頂点で trivial（BM 命題 4.1）。
方針：元の生成類の右持ち上げ判定と余積での安定性を使う。
規約：実際の E 代数モデルを局所的に選ぶ。
使われ方：図式のセルの非循環性の始点。 -/
lemma generatingTrivialCofibrations_component (l : K) :
    let := modelCategory A
    generatingTrivialCofibrations A K ≤
      (trivialCofibrations (operad A).Algebra).inverseImage
        (evaluation (operad A) K l) := by
  let := modelCategory A
  have := modelCategory_cofibrantlyGenerated A
  change generatingTrivialCofibrations A K ≤
    (trivialCofibrations (operad A).Algebra).inverseImage (evaluation (operad A) K l)
  intro X Y f hf
  change (⨆ k, ((projectiveGeneratingTrivialCofibrations A).strictMap
    (operad A).freeAlgebraFunctor).strictMap (free (operad A) K k)) f at hf
  rw [MorphismProperty.iSup_iff] at hf
  obtain ⟨k, hf⟩ := hf
  cases hf with
  | @map X Y f hf =>
    have ht : trivialCofibrations (operad A).Algebra f :=
      (((projectiveGeneratingTrivialCofibrations A).strictMap
        (operad A).freeAlgebraFunctor).le_llp_rlp.trans
          (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated
            ((projectiveGeneratingCofibrations A).strictMap (operad A).freeAlgebraFunctor)
            ((projectiveGeneratingTrivialCofibrations A).strictMap
              (operad A).freeAlgebraFunctor)).symm.le) _ hf
    have : Cofibration f := ⟨ht.1⟩
    have : WeakEquivalence f := ⟨ht.2⟩
    exact mem_trivialCofibrations (Limits.Sigma.map (fun _ : k ⟶ l => f))

/-- 概要：図式の J-cell は全頂点で弱同値（BM 命題 4.1、Hovey §2.1）。
方針：評価の余極限保存と trivial cofibration の余積・押し出し・超限合成安定性。
規約：元の図式の cofibrancy を追加しない。
使われ方：実際の小図式圏への完全なモデル構造の転送。 -/
lemma freeCells_acyclic :
    let := modelCategory A
    SerrePositivity.Quillen.relativeCells.{u} (generatingTrivialCofibrations A K) ≤
      ModelGeneration.EvaluationFamily.detected (evaluation (operad A) K)
        (weakEquivalences (operad A).Algebra) := by
  let := modelCategory A
  change SerrePositivity.Quillen.relativeCells.{u} (generatingTrivialCofibrations A K) ≤
    ModelGeneration.EvaluationFamily.detected (evaluation (operad A) K)
      (weakEquivalences (operad A).Algebra)
  intro X Y f hf l
  have h := ModelGeneration.relativeCells_map_le (evaluation (operad A) K l) _
    (trivialCofibrations (operad A).Algebra)
    (generatingTrivialCofibrations_component A K l) f hf
  have hc : SerrePositivity.Quillen.relativeCells.{u}
      (trivialCofibrations (operad A).Algebra) ≤ trivialCofibrations (operad A).Algebra := by
    rw [← fibrations_llp]
    exact (MorphismProperty.transfiniteCompositions_monotone
      ((MorphismProperty.pushouts_monotone
        (fibrations (operad A).Algebra).llp.coproducts_le).trans
          (fibrations (operad A).Algebra).llp.pushouts_le)).trans
      (fibrations (operad A).Algebra).llp.transfiniteCompositions_le
  exact (hc _ h).2

end SerrePositivity.EInfinity.BarrattEccles.Diagram
