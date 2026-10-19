module
public import SerrePositivity.InfinityCategories.Stable.UniverseJoinNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Core.JoinTensorPoint

/-! # 錐・余錐の標準単体付き join の宇宙比較

概要：join の一因子を標準単体にした形状を大きい宇宙の同じ形状と実同型で比較する。
方針：join の宇宙同型と標準単体の二重 ULift の同型を合成する。
規約：固定図式への包含を保持。使われ方：slice/coslice の宇宙同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
open scoped Simplicial

/-- 大きい宇宙での同じ標準単体へ写す同型は全単調写像と可換。 -/
lemma uliftStdSimplexIso_hom_map {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (SSet.uliftFunctor.{v, u}).map (stdSimplex.map α) ≫ (uliftStdSimplexIso.{u, v} n).hom =
      (uliftStdSimplexIso.{u, v} m).hom ≫ (stdSimplex.map α :
        (Δ[m] : SSet.{max u v}) ⟶ Δ[n]) := rfl

/-- 実錐の形状 join Δ[n] K の宇宙比較。 -/
def uliftConeShapeIso (K : SSet.{u}) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).obj (join (Δ[n] : SSet.{u}) K) ≅
      join (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) :=
  uliftJoinIso Δ[n] K ≪≫ joinIso (uliftStdSimplexIso.{u, v} n) (Iso.refl _)

/-- 実余錐の形状 join K Δ[n] の宇宙比較。 -/
def uliftCoconeShapeIso (K : SSet.{u}) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).obj (join K (Δ[n] : SSet.{u})) ≅
      join ((SSet.uliftFunctor.{v, u}).obj K) (Δ[n] : SSet.{max u v}) :=
  uliftJoinIso K Δ[n] ≪≫ joinIso (Iso.refl _) (uliftStdSimplexIso.{u, v} n)

/-- 錐の形状同型は固定図式側の右包含を保つ。 -/
lemma uliftConeShapeIso_inr (K : SSet.{u}) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).map (joinInr (Δ[n] : SSet.{u}) K) ≫
        (uliftConeShapeIso K n).hom =
      joinInr (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) := by
  unfold uliftConeShapeIso
  simp only [Iso.trans_hom, joinIso, ← Category.assoc, uliftJoinIso_inr,
    joinInr_joinMap, Iso.refl_hom, Category.id_comp]

/-- 余錐の形状同型は固定図式側の左包含を保つ。 -/
lemma uliftCoconeShapeIso_inl (K : SSet.{u}) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).map (joinInl K (Δ[n] : SSet.{u})) ≫
        (uliftCoconeShapeIso K n).hom =
      joinInl ((SSet.uliftFunctor.{v, u}).obj K) (Δ[n] : SSet.{max u v}) := by
  unfold uliftCoconeShapeIso
  simp only [Iso.trans_hom, joinIso, ← Category.assoc, uliftJoinIso_inl,
    joinInl_joinMap, Iso.refl_hom, Category.id_comp]

/-- 錐の逆形状同型も固定図式側の右包含を保つ。 -/
lemma uliftConeShapeIso_inv_inr (K : SSet.{u}) (n : ℕ) :
    joinInr (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) ≫
        (uliftConeShapeIso K n).inv =
      (SSet.uliftFunctor.{v, u}).map (joinInr (Δ[n] : SSet.{u}) K) := by
  rw [← uliftConeShapeIso_inr K n, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 余錐の逆形状同型も固定図式側の左包含を保つ。 -/
lemma uliftCoconeShapeIso_inv_inl (K : SSet.{u}) (n : ℕ) :
    joinInl ((SSet.uliftFunctor.{v, u}).obj K) (Δ[n] : SSet.{max u v}) ≫
        (uliftCoconeShapeIso K n).inv =
      (SSet.uliftFunctor.{v, u}).map (joinInl K (Δ[n] : SSet.{u})) := by
  rw [← uliftCoconeShapeIso_inl K n, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories
