module

public import SerrePositivity.InfinityCategories.F2.Presentable.SourceCosliceCompactness

/-!
概要：任意の一点写像の下の coslice で、compact な始域と終域を持つ指定頂点を compact と判定する。
方針：元の一点写像を Yoneda 表示し、元の余錐の脚から同じ射を回収する。
規約：頂点や構造射を同型な別の対象へ選び直さない。
使われ方：指定表示段からの元の構造射への相対因子化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：compact な始域・終域の指定余錐は元の一点 coslice 内でも compact。
方針：元の脚の辺を回収し、辺からの coslice 頂点が元の頂点と厳密に等しいことを使う。
規約：元の一点写像の任意の表示を許す。
使われ方：途中段からの射を保った compact 切断。 -/
lemma isKappaCompact_pointCosliceVertex
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C]
    (p : (Δ[0] : SSet.{u + 1}) ⟶ C) (c : JoinCocone p)
    (hp : Compact.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv p))
    (hc : Compact.IsKappaCompact.{u, u + 1} μ c.vertex) :
    Compact.IsKappaCompact.{u, u + 1} μ (C := sliceUnder p) c := by
  obtain ⟨x, rfl⟩ := SSet.yonedaEquiv.symm.surjective p
  have hx : Compact.IsKappaCompact.{u, u + 1} μ x := by
    simpa only [Equiv.apply_symm_apply] using hp
  let l := c.leg (𝟙 Δ[0])
  let e : C.Edge x c.vertex :=
    { edge := l.edge
      src_eq := by
        change C.δ 1 l.edge = x
        have h := l.src_eq
        change C.δ 1 l.edge = SSet.yonedaEquiv (𝟙 Δ[0] ≫ SSet.yonedaEquiv.symm x) at h
        simpa only [Category.id_comp, Equiv.apply_symm_apply] using h
      tgt_eq := l.tgt_eq }
  have he : edgeCosliceVertex e.toTruncated = c := by
    apply Subtype.ext
    change (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
        joinMap (𝟙 Δ[0]) (𝟙 Δ[0]) ≫ c.val)) = c.val
    rw [Equiv.symm_apply_apply, joinMap_id, Category.id_comp, Iso.hom_inv_id_assoc]
  have h := isKappaCompact_edgeCosliceVertex hμ e hx hc
  rwa [he] at h

end SerrePositivity.InfinityCategories.F2.Presentable
