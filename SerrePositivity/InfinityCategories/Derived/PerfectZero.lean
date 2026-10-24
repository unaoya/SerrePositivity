module
public import SerrePositivity.InfinityCategories.Derived.PerfectBasic
public import SerrePositivity.InfinityCategories.Derived.SemifreeLimits

/-! # Perf の零対象

概要：零複体の頂点は Perf の始対象かつ終対象である。
方針：充満 dg 部分圏での反映を用い、正本への単体的同型で境界充填を移す。
規約：高次の境界充填による始対象性と終対象性。使われ方：Perf の零対象。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
open scoped Simplicial ZeroObject
variable (S : Type u) [CommRing S]

/-- 概要：計算モデルの零頂点。
方針：零複体の定値頂点を取る。
規約：完全 semifree 代表。使われ方：零対象の充填。 -/
def perfectNerveZero : (perfectNerveModel S) _⦋0⦌ := Simplex.vertex (perfectSemifreeZero S)

/-- 概要：計算モデルの零頂点は終対象である。
方針：semifree の零頂点の終対象性を充満包含で反映する。
規約：任意の可換環。使われ方：正本の終対象性。 -/
lemma perfectNerveZero_terminal : IsTerminalVertex (perfectNerveZero S) := by
  apply isTerminalVertex_of_fullInclusion S (Semifree S) (perfectSemifreeProperty S)
  have hv : (perfectNerveInclusion S).app _ (perfectNerveZero S) =
      Simplex.vertex (⟨0, complexSemifree_zero S⟩ : Semifree S) := by
    apply Simplex.vertexEquiv.injective
    rfl
  change IsTerminalVertex ((perfectNerveInclusion S).app _ (perfectNerveZero S))
  rw [hv]
  exact isTerminalVertex_semifree_zero S

/-- 概要：計算モデルの零頂点は始対象である。
方針：semifree の零頂点の始対象性を充満包含で反映する。
規約：高次の境界充填。使われ方：正本の始対象性。 -/
lemma perfectNerveZero_initial : IsInitialVertex (perfectNerveZero S) := by
  apply isInitialVertex_of_fullInclusion S (Semifree S) (perfectSemifreeProperty S)
  have hv : (perfectNerveInclusion S).app _ (perfectNerveZero S) =
      Simplex.vertex (⟨0, complexSemifree_zero S⟩ : Semifree S) := by
    apply Simplex.vertexEquiv.injective
    rfl
  change IsInitialVertex ((perfectNerveInclusion S).app _ (perfectNerveZero S))
  rw [hv]
  exact isInitialVertex_semifree_zero S

/-- 概要：正本の Perf の零頂点。
方針：計算モデルの零頂点を標準同型で移す。
規約：D(S) の部分型の頂点。使われ方：Perf の零対象。 -/
def perfectInfinityZero : (perfectInfinityCategory S) _⦋0⦌ :=
  (perfectNerveModelIso S).hom.app _ (perfectNerveZero S)

private lemma iso_inverse_vertex : (perfectNerveModelIso S).inv.app _ (perfectInfinityZero S) =
    perfectNerveZero S := by
  change ((perfectNerveModelIso S).hom ≫ (perfectNerveModelIso S).inv).app _ _ = _
  rw [Iso.hom_inv_id]
  rfl

/-- 概要：正本の Perf の零頂点は終対象である。
方針：単体的同型で移した境界を計算モデルで充填する。
規約：D(S) の部分としての実際の頂点。使われ方：零対象の終対象性。 -/
lemma perfectInfinityZero_terminal : IsTerminalVertex (perfectInfinityZero S) := by
  intro n b hb
  have hb' : boundaryVertex n (Fin.last (n + 1)) ≫ (b ≫ (perfectNerveModelIso S).inv) =
      SSet.yonedaEquiv.symm (perfectNerveZero S) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp, iso_inverse_vertex]
  obtain ⟨f, hf⟩ := perfectNerveZero_terminal S n _ hb'
  refine ⟨f ≫ (perfectNerveModelIso S).hom, ?_⟩
  rw [← Category.assoc, hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：正本の Perf の零頂点は始対象である。
方針：単体的同型で移した境界を計算モデルで充填する。
規約：始点を固定する境界条件。使われ方：零対象の始対象性。 -/
lemma perfectInfinityZero_initial : IsInitialVertex (perfectInfinityZero S) := by
  intro n b hb
  have hb' : boundaryVertex n 0 ≫ (b ≫ (perfectNerveModelIso S).inv) =
      SSet.yonedaEquiv.symm (perfectNerveZero S) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp, iso_inverse_vertex]
  obtain ⟨f, hf⟩ := perfectNerveZero_initial S n _ hb'
  refine ⟨f ≫ (perfectNerveModelIso S).hom, ?_⟩
  rw [← Category.assoc, hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.InfinityCategories
