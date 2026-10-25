module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedSource

/-!
概要：固定始域の飽和射圏の全ての実辺は、元の強飽和生成閉包へ写る。
方針：coslice の脚の実合成二単体に、生成閉包の二つから三つの消去を適用する。
規約：ホモトピー圏の任意の代表へ置換せず、元の指定辺を保持する。
使われ方：HTT 5.5.5.14 の終対象から局所性への工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 固定始域の閉包内射の間の指定辺は、終域射影で元の生成閉包に入る。 -/
lemma generatedSourceEdge_mem (edges : I → C _⦋1⦌) (x : C _⦋0⦌)
    {s t : (generatedSourceCategory edges x) _⦋0⦌}
    (e : (generatedSourceCategory edges x).Edge s t) :
    (e.map (generatedSourceTarget edges x)).edge ∈ generatedEdges edges := by
  let f := e.map (generatedSourceInclusion edges x)
  have hs := fullSubcomplexOnVertices_vertex s
  have ht := fullSubcomplexOnVertices_vertex t
  exact (stronglySaturatedClosure_stronglySaturated
    (SSet.uliftFunctor.{u + 1, u}).obj (Set.range edges)).2.2.2.2.1
      (JoinCocone.legCompStruct f.toTruncated (𝟙 Δ[0])) hs ht

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
