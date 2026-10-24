module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorVertexCone
public import SerrePositivity.InfinityCategories.Core.LimitConeExtension
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits

/-!
概要：関手頂点からの元の錐の読み戻しは形状の制限と交換し、同型形状では極限性を保つ。
方針：関手頂点の全単射の往復と、元の slice の同型による制限を使う。
規約：元の錐の全単体を保持。使われ方：coherent filtered 交換の形状同型不変性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 関手頂点から射への読み戻しは元のパラメータの前合成と交換する。 -/
lemma functorVertexMap_precomp {J K X : SSet.{u}} (f : J ⟶ K)
    (v : ((ihom K).obj X) _⦋0⦌) :
    (functorVertexEquiv J X).symm (((pre f).app X).app (Opposite.op ⦋0⦌) v) =
      f ≫ (functorVertexEquiv K X).symm v := by
  obtain ⟨g, rfl⟩ := (functorVertexEquiv K X).surjective v
  change (functorVertexEquiv J X).symm ((functorVertexEquiv J X) (f ≫ g)) =
    f ≫ (functorVertexEquiv K X).symm ((functorVertexEquiv K X) g)
  simp only [Equiv.symm_apply_apply]

/-- 錐形状の関手頂点の読み戻しは元の部分形状への制限と厳密に交換する。 -/
lemma functorVertexConeMap_precomp {J K X : SSet.{u}} (f : J ⟶ K)
    (v : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌) :
    functorVertexConeMap (((pre (joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X).app
      (Opposite.op ⦋0⦌) v) = joinMap (𝟙 Δ[0]) f ≫ functorVertexConeMap v :=
  functorVertexMap_precomp _ v

/-- 形状同型による元の錐の制限は極限性を保存・反映する。 -/
lemma isLimitCone_restrict_iff_of_isIso {J K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (f : J ⟶ K) [IsIso f] :
    IsLimitCone (restrictJoinCone c f) ↔ IsLimitCone c := by
  have : IsIso (sliceOverRestrict p f) := sliceOverRestrict_isIso p f
  constructor
  · intro h
    exact isTerminalVertex_of_trivialKanFibration (sliceOverRestrict p f) h
  · intro h
    exact h.map_of_isIso (sliceOverRestrict p f)

/-- 同型形状への前合成後に読み戻した元の関手頂点の錐も、同じ極限性を持つ。 -/
lemma isLimitCone_functorVertexCone_reindex_iff {J K X : SSet.{u}} (f : J ⟶ K) [IsIso f]
    (v : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌) :
    IsLimitCone (functorVertexCone (((pre (joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X).app
      (Opposite.op ⦋0⦌) v)) ↔ IsLimitCone (functorVertexCone v) := by
  let c := functorVertexCone v
  let d := functorVertexCone (((pre (joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X).app
    (Opposite.op ⦋0⦌) v)
  let e := restrictJoinCone c f
  have hval : d.val = e.val := functorVertexConeMap_precomp f v
  have hp := d.property.symm.trans
    ((congrArg (fun k => joinInr (Δ[0] : SSet.{u}) J ≫ k) hval).trans e.property)
  exact (isLimitCone_iff_of_diagram_eq (c := d) (d := e) hp hval).trans
    (isLimitCone_restrict_iff_of_isIso c f)

end SerrePositivity.InfinityCategories.F2
