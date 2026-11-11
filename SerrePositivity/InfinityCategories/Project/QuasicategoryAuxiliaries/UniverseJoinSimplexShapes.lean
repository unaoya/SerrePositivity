module
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseJoinNaturality
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-! # 錐・余錐の標準単体付き join の宇宙比較

概要：join の一因子を標準単体にした形状を大きい宇宙の同じ形状と実同型で比較する。
方針：join の宇宙同型と標準単体の二重 ULift の同型を合成する。
規約：固定図式への包含を保持。使われ方：slice/coslice の宇宙同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet
open scoped _root_.Simplicial

/-- 大きい宇宙での同じ標準単体へ写す同型は全単調写像と可換。 -/
lemma uliftStdSimplexIso_hom_map {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (SSet.uliftFunctor.{v, u}).map (stdSimplex.map α) ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} m).hom ≫ (stdSimplex.map α :
        (Δ[m] : SSet.{max u v}) ⟶ Δ[n]) := rfl

/-- 実錐の形状 join Δ[n] K の宇宙比較。 -/
def uliftConeShapeIso (K : SSet.{u}) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) K) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso Δ[n] K ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n) (Iso.refl _)

/-- 実余錐の形状 join K Δ[n] の宇宙比較。 -/
def uliftCoconeShapeIso (K : SSet.{u}) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[n] : SSet.{u})) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{v, u}).obj K) (Δ[n] : SSet.{max u v}) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso K Δ[n] ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} n)

/-- 錐の形状同型は固定図式側の右包含を保つ。 -/
lemma uliftConeShapeIso_inr (K : SSet.{u}) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) K) ≫
        (uliftConeShapeIso K n).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) := by
  unfold uliftConeShapeIso
  simp only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_inr,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Iso.refl_hom, Category.id_comp]

/-- 余錐の形状同型は固定図式側の左包含を保つ。 -/
lemma uliftCoconeShapeIso_inl (K : SSet.{u}) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[n] : SSet.{u})) ≫
        (uliftCoconeShapeIso K n).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{v, u}).obj K) (Δ[n] : SSet.{max u v}) := by
  unfold uliftCoconeShapeIso
  simp only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_inl,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Iso.refl_hom, Category.id_comp]

/-- 錐の逆形状同型も固定図式側の右包含を保つ。 -/
lemma uliftConeShapeIso_inv_inr (K : SSet.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) ≫
        (uliftConeShapeIso K n).inv =
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) K) := by
  rw [← uliftConeShapeIso_inr K n, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- 余錐の逆形状同型も固定図式側の左包含を保つ。 -/
lemma uliftCoconeShapeIso_inv_inl (K : SSet.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl ((SSet.uliftFunctor.{v, u}).obj K) (Δ[n] : SSet.{max u v}) ≫
        (uliftCoconeShapeIso K n).inv =
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[n] : SSet.{u})) := by
  rw [← uliftCoconeShapeIso_inl K n, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
