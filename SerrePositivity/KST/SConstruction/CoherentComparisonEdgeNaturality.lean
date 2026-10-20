module
public import SerrePositivity.KST.SConstruction.CoherentPathInsertion

/-! # 元の coherent 合成比較辺の全単体作用素との可換性
概要：元の長辺から合成への比較辺は、面・退化を含む全再添字で同じ実辺を回収する。
方針：端点 Path と三頂点 Path の再添字を照合し、元の包含射全体を写す。
規約：辺の代表を選び直さず、端点が潰れる順序写像も含める。
使われ方：三入力の実二単体の辺を保存した同じ合成面の復号辺へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 三頂点の合成 Path は、端点が潰れる場合も含めて全再添字と可換。 -/
lemma coherentEndpointPathComposite_map {J K : Type u} [LinearOrder J] [LinearOrder K]
    (θ : J →o K) {a b c : J} (hab : a ≤ b) (hbc : b ≤ c) :
    (SimplicialThickening.functorMap θ (.mk a) (.mk c)).obj
        (coherentEndpointPathComposite hab hbc) =
      coherentEndpointPathComposite (θ.monotone hab) (θ.monotone hbc) := by
  rw [← coherentPathInsert_endpoint, coherentPathInsert_map, coherentEndpointPath_map,
    coherentPathInsert_endpoint]

/-- 元の長辺から合成への全包含辺を再添字すると、同じ包含辺を回収する。 -/
lemma coherentEndpointPathToComposite_map_edge
    {J K : Type u} [LinearOrder J] [LinearOrder K] (θ : J →o K)
    {a b c : J} (hab : a ≤ b) (hbc : b ≤ c) :
    (nerveMap (SimplicialThickening.functorMap θ (.mk a) (.mk c))).app (Opposite.op ⦋1⦌)
        (nerve.edgeMk (coherentEndpointPathToComposite hab hbc)).edge =
      (nerve.edgeMk (coherentEndpointPathToComposite (θ.monotone hab)
        (θ.monotone hbc))).edge := by
  refine ComposableArrows.ext₁ (coherentEndpointPath_map θ (hab.trans hbc))
    (coherentEndpointPathComposite_map θ hab hbc) ?_
  apply InducedCategory.hom_ext
  exact Subsingleton.elim _ _

/-- 元の全合成比較辺は、全単体作用素に沿う面・退化の復号と厳密に可換。 -/
lemma coherentSimplexCompositionEdge_naturality
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {m n : ℕ} (s : (SimplicialNerve C) _⦋n⦌) (θ : ⦋m⦌ ⟶ ⦋n⦌)
    (i j k : Fin (m + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    (coherentSimplexCompositionEdge ((SimplicialNerve C).map θ.op s) i j k hij hjk).edge =
      (coherentSimplexCompositionEdge s (θ.toOrderHom i) (θ.toOrderHom j) (θ.toOrderHom k)
        (θ.toOrderHom.monotone hij) (θ.toOrderHom.monotone hjk)).edge := by
  change (s.map _ _).app (Opposite.op ⦋1⦌)
    ((nerveMap (SimplicialThickening.functorMap θ.toOrderHom.uliftMap _ _)).app
      (Opposite.op ⦋1⦌) (nerve.edgeMk (coherentEndpointPathToComposite
        (show (ULift.up i : ULift.{u} _) ≤ ULift.up j from hij)
        (show (ULift.up j : ULift.{u} _) ≤ ULift.up k from hjk))).edge) = _
  rw [coherentEndpointPathToComposite_map_edge]
  rfl

end SerrePositivity.KST.SConstruction
