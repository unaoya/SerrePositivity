module

public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaPrism
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaRestriction

/-!
概要：元の全図式 comma の全円柱は試験族・図式形状の両制限に厳密に自然。
方針：元の全余錐の制限と内部 Hom の随伴の自然性を合成する。
規約：元の C 側の全図式と指定 D の全変換を保持する。
使われ方：下方余錐から元の旧族の slice 円柱へ制限する境界の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {K C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ IndInfinity κ C)
/-- 概要：元の全円柱の試験族制限は全変換を厳密に保つ。
方針：同じ標準全余錐の自然性。規約：全射の等号。使われ方：点追加の共通境界。 -/
lemma diagramCommaPrism_precomp {T T₀ : SSet.{u + 1}} (q : T ⟶ diagramComma κ D)
    (g : T₀ ⟶ T) :
    ((SSet.uliftFunctor.{u + 1, u}).obj K ◁ joinMap g (𝟙 (Δ[0] : SSet.{u + 1}))) ≫
      diagramCommaPrism κ D q = diagramCommaPrism κ D (g ≫ q) := by
  simp only [diagramCommaPrism, ← uncurry_natural_left, ← Category.assoc,
    ← joinMap_comp, Category.id_comp]
/-- 概要：元の全円柱の形状制限は元の図式 comma の制限と一致する。
方針：同じ標準全余錐の自然性。規約：全射の等号。使われ方：点追加の共通境界。 -/
lemma diagramCommaPrism_restrict {J : SSet.{u}} (f : J ⟶ K)
    {T : SSet.{u + 1}} (q : T ⟶ diagramComma κ D) :
    ((SSet.uliftFunctor.{u + 1, u}).map f ▷ join T (Δ[0] : SSet.{u + 1})) ≫
      diagramCommaPrism κ D q =
    diagramCommaPrism κ ((SSet.uliftFunctor.{u + 1, u}).map f ≫ D)
      (q ≫ diagramCommaRestriction κ D f) := by
  rw [diagramCommaPrism, diagramCommaPrism, ← uncurry_pre_app]
  apply congrArg uncurry
  have h := congrArg (fun a ↦ joinMap q (𝟙 (Δ[0] : SSet.{u + 1})) ≫ a)
    (diagramCommaRestriction_coconeMap κ D f)
  simp only [← Category.assoc, ← joinMap_comp, Category.id_comp] at h
  simpa only [Category.assoc] using h.symm
end SerrePositivity.InfinityCategories.F2.Ind
