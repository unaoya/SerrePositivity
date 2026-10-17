module
public import SerrePositivity.InfinityCategories.DGNerve.FullInclusionExtension
public import SerrePositivity.InfinityCategories.DGNerve.ZeroObject

/-! # 充満 dg 部分圏の零対象

概要：充満 dg 部分圏の包含は始対象性・終対象性を反映し、零複体を含む部分圏は零対象を持つ。
方針：周囲で正次元境界を充填し、全頂点を覆う境界からその充填を持ち上げる。
規約：HTT §1.2.12、HA Construction 1.3.1.6。使われ方：導来 ∞ 圏の零対象。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded
open scoped Simplicial ZeroObject

variable (A : Type u) [CommRing A]

/-- 概要：充満 dg 部分圏の包含は Terminal 頂点の充填条件を反映する。
方針：周囲の境界充填を、全頂点を覆う境界に沿って部分圏へ持ち上げる。
規約：HTT §1.2.12。使われ方：零対象の Terminal 性を部分圏へ戻す。 -/
lemma isTerminalVertex_of_fullInclusion (D : Type v) [DGCategory A D] (P : D → Prop)
    (x : (dgNerve A (DGFullSubcategory D P)) _⦋0⦌)
    (hx : IsTerminalVertex ((dgNerve.map (dgFullSubcategoryInclusion A D P)).app _ x)) :
    IsTerminalVertex x := by
  intro n b hb
  let q := dgNerve.map (dgFullSubcategoryInclusion A D P)
  have hb' : boundaryVertex n (Fin.last (n + 1)) ≫ (b ≫ q) =
      SSet.yonedaEquiv.symm (q.app _ x) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
  obtain ⟨F, hF⟩ := hx n (b ≫ q) hb'
  obtain ⟨L, hL, _⟩ := fullInclusion_extension A D P (SSet.boundary (n + 1)).ι
    (boundary_vertices_surjective n) b F hF
  exact ⟨L, hL⟩

/-- 概要：零複体を含む充満部分圏の零複体の頂点は Terminal 対象。
方針：周囲の零複体の Terminal 性を包含で反映する。
規約：HTT §1.2.12。使われ方：Semifree などの dg nerve の零対象。 -/
lemma isTerminalVertex_full_zero (P : Complex A → Prop) (hzero : P (0 : Complex A)) :
    IsTerminalVertex (X := dgNerve A (DGFullSubcategory (Complex A) P))
      (Simplex.vertex (⟨0, hzero⟩ : DGFullSubcategory (Complex A) P)) := by
  apply isTerminalVertex_of_fullInclusion A (Complex A) P
  have hv : (Simplex.vertex (⟨0, hzero⟩ : DGFullSubcategory (Complex A) P)).map
      (dgFullSubcategoryInclusion A (Complex A) P) = Simplex.vertex (0 : Complex A) := by
    apply Simplex.vertexEquiv.injective
    rfl
  change IsTerminalVertex (X := dgNerve A (Complex A))
    ((Simplex.vertex (⟨0, hzero⟩ : DGFullSubcategory (Complex A) P)).map
    (dgFullSubcategoryInclusion A (Complex A) P))
  rw [hv]
  exact isTerminalVertex_zero A

/-- 概要：充満 dg 部分圏の包含は Initial 頂点の充填条件を反映する。
方針：周囲の境界充填を、全頂点を覆う境界に沿って部分圏へ持ち上げる。
規約：HTT §1.2.12。使われ方：零対象の Initial 性を部分圏へ戻す。 -/
lemma isInitialVertex_of_fullInclusion (D : Type v) [DGCategory A D] (P : D → Prop)
    (x : (dgNerve A (DGFullSubcategory D P)) _⦋0⦌)
    (hx : IsInitialVertex ((dgNerve.map (dgFullSubcategoryInclusion A D P)).app _ x)) :
    IsInitialVertex x := by
  intro n b hb
  let q := dgNerve.map (dgFullSubcategoryInclusion A D P)
  have hb' : boundaryVertex n (0) ≫ (b ≫ q) =
      SSet.yonedaEquiv.symm (q.app _ x) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
  obtain ⟨F, hF⟩ := hx n (b ≫ q) hb'
  obtain ⟨L, hL, _⟩ := fullInclusion_extension A D P (SSet.boundary (n + 1)).ι
    (boundary_vertices_surjective n) b F hF
  exact ⟨L, hL⟩

/-- 概要：零複体を含む充満部分圏の零複体の頂点は Initial 対象。
方針：周囲の零複体の Initial 性を包含で反映する。
規約：HTT §1.2.12。使われ方：Semifree などの dg nerve の零対象。 -/
lemma isInitialVertex_full_zero (P : Complex A → Prop) (hzero : P (0 : Complex A)) :
    IsInitialVertex (X := dgNerve A (DGFullSubcategory (Complex A) P))
      (Simplex.vertex (⟨0, hzero⟩ : DGFullSubcategory (Complex A) P)) := by
  apply isInitialVertex_of_fullInclusion A (Complex A) P
  have hv : (Simplex.vertex (⟨0, hzero⟩ : DGFullSubcategory (Complex A) P)).map
      (dgFullSubcategoryInclusion A (Complex A) P) = Simplex.vertex (0 : Complex A) := by
    apply Simplex.vertexEquiv.injective
    rfl
  change IsInitialVertex (X := dgNerve A (Complex A))
    ((Simplex.vertex (⟨0, hzero⟩ : DGFullSubcategory (Complex A) P)).map
    (dgFullSubcategoryInclusion A (Complex A) P))
  rw [hv]
  exact isInitialVertex_zero A

end SerrePositivity.InfinityCategories.DGNerve
