module
public import SerrePositivity.InfinityCategories.Derived.DGModuleKappaCompactShift
public import SerrePositivity.InfinityCategories.Derived.DGKappaSpanPosetShape
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallPosetColimitCompactUniverse
public import SerrePositivity.InfinityCategories.Core.ColimitReindex
public import SerrePositivity.InfinityCategories.Stable.PushoutComparisonCorners
public import SerrePositivity.InfinityCategories.F1.CoconeMappingPiZero
/-!
概要：非可算正則 κ について、実閉加群射の同じ cone の実導来頂点は κ-compact で閉じる。
方針：実押し出しの span を小 poset に厳密制限し、P-9 の同じ κ による余極限閉性を使う。
規約：ordinary compact で代用せず、追加の交換入力・射影性・有限存在仮定を置かない。
使われ方：D-8 c4 の任意閉射 cone 入力と、実分解が保つ押し出しへの適用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet MonoidalCategory
open SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
variable {κ : Cardinal.{u}} [hreg : Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
include hreg hκ

/-- 同じ実導来 ∞ 圏の span の指定余極限は、同じ κ の compact 頂点で閉じる。 -/
lemma dgModuleDerived_spanColimit_isKappaCompact
    {p : (horn 2 0 : SSet.{max (u + 1) v}) ⟶ dgModuleDerivedInfinityCategory R D}
    (c : JoinCocone p) (hc : IsColimitCone c)
    (hp : ∀ k, F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ (p.app _ k)) :
    F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ c.vertex := by
  let e := dgKappaSpanPosetHornIso.{u, max (u + 1) v}
  have hs := F2.Presentable.isKappaCompact_smallPosetColimit_universe.{u, max (u + 1) v}
    hκ DGKappaSpanPoset (hasCardinalLT_of_finite _ _ hκ.le)
    (c.restrict e.hom) ((isColimitCone_iff_restrict_of_isIso c e.hom).mp hc)
    (fun k ↦ hp (e.hom.app _ k))
  have hv : (c.restrict e.hom).vertex = c.vertex := by
    rw [JoinCocone.vertex_eq, JoinCocone.vertex_eq]
    change SSet.yonedaEquiv (joinInr _ _ ≫ (joinMap e.hom (𝟙 _) ≫ c.val)) = _
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp]
  exact hv ▸ hs

/-- 同じ実導来 ∞ 圏の押し出しは、入力三頂点の κ-compact 性から残る頂点も κ-compact。 -/
lemma dgModuleDerived_pushout_isKappaCompact
    (S : Δ[1] ⊗ Δ[1] ⟶ dgModuleDerivedInfinityCategory R D) (hS : IsPushoutSquare S)
    (h00 : F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ (squareVertex S 0 0))
    (h10 : F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ (squareVertex S 1 0))
    (h01 : F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ (squareVertex S 0 1)) :
    F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ (squareVertex S 1 1) := by
  have h := dgModuleDerived_spanColimit_isKappaCompact R D hκ (pushoutCocone S) hS (fun k ↦ ?_)
  · rwa [pushoutCocone_vertex] at h
  · change F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ
      (S.app _ (spanSquareBoundary.app _ k))
    rcases spanSquareBoundary_vertex_cases k with h | h | h
    · rw [h]; exact h00
    · rw [h]; exact h10
    · rw [h]; exact h01

/-- 元の任意の閉加群射の実 cone は、同じ実導来 ∞ 圏で κ-compact 性を保つ。 -/
lemma dgModuleKappaCompact_cone {M N : ModuleCategory R D}
    (hM : dgModuleKappaCompact R D κ M) (hN : dgModuleKappaCompact R D κ N) (f : M ⟶ N) :
    dgModuleKappaCompact R D κ (moduleCone R D f) := by
  have h := dgModuleDerived_pushout_isKappaCompact R D hκ
    (dgModuleConeSquare R D f ≫ dgConeModuleDerived R D)
    (dgConeModuleDerived_coneSquare_isPushout R D f) ?_ ?_ ?_
  · rwa [dgConeModuleDerived_coneSquare_vertex] at h
  · change F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ
      ((dgConeModuleDerived R D).app _ (squareVertex (dgModuleConeSquare R D f) 0 0))
    rw [dgModuleConeSquare_vertex00]; exact hM
  · change F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ
      ((dgConeModuleDerived R D).app _ (squareVertex (dgModuleConeSquare R D f) 1 0))
    rw [dgModuleConeSquare_vertex10]; exact hN
  · change F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ
      ((dgConeModuleDerived R D).app _ (squareVertex (dgModuleConeSquare R D f) 0 1))
    rw [dgModuleConeSquare_vertex01]
    exact dgModuleKappaCompact_zero R D hκ.le

end SerrePositivity.InfinityCategories
