module
public import SerrePositivity.InfinityCategories.Stable.UniverseJoinSimplexShapes

/-! # 標準単体付き join の宇宙同型と全単体作用

概要：錐・余錐の形状同型は全ての単調写像による可変因子の引き戻しと可換。
方針：join の自然性と標準単体の宇宙同型の自然性を合成する。
規約：面と退化を同時に扱う。使われ方：slice/coslice の宇宙同型の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
open scoped Simplicial

/-- 錐の形状の順同型は可変標準単体の全単調写像と可換。 -/
lemma uliftConeShapeIso_hom_map (K : SSet.{u}) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (SSet.uliftFunctor.{v, u}).map (joinMap (stdSimplex.map α) (𝟙 K)) ≫
        (uliftConeShapeIso K n).hom =
      (uliftConeShapeIso K m).hom ≫
        joinMap (stdSimplex.map α) (𝟙 ((SSet.uliftFunctor.{v, u}).obj K)) := by
  unfold uliftConeShapeIso
  simp only [Iso.trans_hom, joinIso, Iso.refl_hom]
  rw [← Category.assoc, uliftJoinIso_hom_naturality]
  simp only [Category.assoc]
  rw [← joinMap_comp, ← joinMap_comp, uliftStdSimplexIso_hom_map]
  rw [(SSet.uliftFunctor.{v, u}).map_id K]

/-- 余錐の形状の順同型は可変標準単体の全単調写像と可換。 -/
lemma uliftCoconeShapeIso_hom_map (K : SSet.{u}) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (SSet.uliftFunctor.{v, u}).map (joinMap (𝟙 K) (stdSimplex.map α)) ≫
        (uliftCoconeShapeIso K n).hom =
      (uliftCoconeShapeIso K m).hom ≫
        joinMap (𝟙 ((SSet.uliftFunctor.{v, u}).obj K)) (stdSimplex.map α) := by
  unfold uliftCoconeShapeIso
  simp only [Iso.trans_hom, joinIso, Iso.refl_hom]
  rw [← Category.assoc, uliftJoinIso_hom_naturality]
  simp only [Category.assoc]
  rw [← joinMap_comp, ← joinMap_comp, uliftStdSimplexIso_hom_map]
  rw [(SSet.uliftFunctor.{v, u}).map_id K]

private lemma inverse_naturality {C : Type*} [Category* C] {X Y X' Y' : C}
    (a : X ≅ Y) (b : X' ≅ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ b.hom = a.hom ≫ g) : g ≫ b.inv = a.inv ≫ f := by
  apply (cancel_epi a.hom).1
  rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.hom_inv_id_assoc]

/-- 錐の逆形状同型も全単体作用と可換。 -/
lemma uliftConeShapeIso_inv_map (K : SSet.{u}) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    joinMap (stdSimplex.map α) (𝟙 ((SSet.uliftFunctor.{v, u}).obj K)) ≫
        (uliftConeShapeIso K n).inv =
      (uliftConeShapeIso K m).inv ≫
        (SSet.uliftFunctor.{v, u}).map (joinMap (stdSimplex.map α) (𝟙 K)) :=
  inverse_naturality _ _ _ _ (uliftConeShapeIso_hom_map K α)

/-- 余錐の逆形状同型も全単体作用と可換。 -/
lemma uliftCoconeShapeIso_inv_map (K : SSet.{u}) {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    joinMap (𝟙 ((SSet.uliftFunctor.{v, u}).obj K)) (stdSimplex.map α) ≫
        (uliftCoconeShapeIso K n).inv =
      (uliftCoconeShapeIso K m).inv ≫
        (SSet.uliftFunctor.{v, u}).map (joinMap (𝟙 K) (stdSimplex.map α)) :=
  inverse_naturality _ _ _ _ (uliftCoconeShapeIso_hom_map K α)

end SerrePositivity.InfinityCategories
