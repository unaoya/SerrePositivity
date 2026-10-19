module
public import SerrePositivity.InfinityCategories.Derived.FullInclusionHomotopyFaithful
public import SerrePositivity.InfinityCategories.Derived.ChainMapEdge

/-! # 通常の h D(S) の射の鎖写像代表

概要：定値頂点間の h D(S) のすべての射を実際の鎖写像で表す。
方針：辺の代表を取り、包含後に鎖写像を読み戻して、h 上の忠実性で戻す。
規約：任意の semifree 複体。使われ方：D7 の自然性をすべての h の射へ拡張する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable {S : Type u} [CommRing S] {X Y : Semifree S}

/-- 通常の h D(S) の定値頂点間の射は鎖写像の辺の類で代表される。 -/
lemma derivedHomotopyHom_chainMap_surjective
    (f : (SSet.HomotopyCategory.mk (Simplex.vertex X) :
      hoFunctor.obj (derivedInfinityCategory S)) ⟶ SSet.HomotopyCategory.mk (Simplex.vertex Y)) :
    ∃ a : X.val ⟶ Y.val,
      SSet.Truncated.HomotopyCategory.homMk
        (derivedChainMapEdge (x := Simplex.vertex X) (y := Simplex.vertex Y) a) = f := by
  let : (hoFunctor.map (derivedInfinityInclusion (S := S))).toFunctor.Faithful :=
    fullInclusionHo_faithful S (Complex S) (complexSemifree S)
  obtain ⟨e, rfl⟩ := homotopyCategory_homMk_surjective _ _ f
  let d := e.map ((truncation 2).map derivedInfinityInclusion)
  refine ⟨edgeChainMap d, ?_⟩
  apply (hoFunctor.map derivedInfinityInclusion).toFunctor.map_injective
  apply Arrow.mk_injective
  apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
  exact (derivedChainMapEdge_inclusion (x := Simplex.vertex X) (y := Simplex.vertex Y)
    (edgeChainMap d)).trans (derived_complexEdge_edgeChainMap d)

end SerrePositivity.InfinityCategories
