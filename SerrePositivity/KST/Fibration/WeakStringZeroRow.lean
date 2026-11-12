module
public import SerrePositivity.KST.Fibration.WeakStringConstantPostcomposition
public import SerrePositivity.KST.Fibration.WeakStringVertexPostcomposition
public import SerrePositivity.KST.Comparison.DiagonalRowEvaluation
public import SerrePositivity.KST.Comparison.CylinderBoundary

/-! # 元の W 列の零行評価と元の定数包含の厳密な照合 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Comparison
namespace SerrePositivity.KST.Fibration

/-- 元の零長同型は唯一の頂点の評価を回収する。 -/
lemma weakStringZeroAmbientIso_hom {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakStringZeroAmbientIso q).hom = weakStringVertexExact q ⦋0⦌ 0 := by
  apply Subtype.ext
  rfl

/-- 元の零長同型は包含側の完全関手に関して厳密に自然。 -/
lemma weakStringZeroAmbientIso_postcomp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakStringPostExact f q ⦋0⦌ ≫ (weakStringZeroAmbientIso q).hom =
      (weakStringZeroAmbientIso (f ≫ q : A ⟶ C)).hom ≫ sInputExactMap f := by
  rw [weakStringZeroAmbientIso_hom, weakStringZeroAmbientIso_hom]
  exact weakStringVertexExact_postcomp f q ⦋0⦌ 0

/-- 零行と零次標準単体の積を、元の入力の同じ実現へ戻す厳密同型。 -/
def weakStringRealizationZeroRowIso (F : StableModel.{u} ⥤ SSet.{u})
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    F.obj (weakStringModel q ⦋0⦌) ⊗ Δ[0] ≅ F.obj (sInputModel B) :=
  simplexZeroTensorIso _ ≪≫ F.mapIso (weakStringZeroAmbientIso q)

/-- 全入力を保つ元の零行評価は、零行同型の後の元の定数包含そのもの。 -/
theorem weakStringRealizationZeroRow_evaluation (F : StableModel.{u} ⥤ SSet.{u})
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    diagonalRowEvaluation (weakStringStableSimplicial q ⋙ F) 0 =
      (weakStringRealizationZeroRowIso F q).hom ≫
        weakStringRealizationConstantDiagonal F q := by
  have he (n : SimplexCategory) : (weakStringZeroAmbientIso q).hom ≫
      weakStringConstantExact q n =
        weakStringExactMap q (SimplexCategory.const n ⦋0⦌ 0) := by
    unfold weakStringConstantExact
    rw [Iso.hom_inv_id_assoc]
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  change (F.obj (weakStringModel q ⦋0⦌)).obj d at x
  change (F.map (weakStringExactMap q (stdSimplex.objEquiv t))).app d x =
    (F.map (weakStringConstantExact q d.unop)).app d
      ((F.map (weakStringZeroAmbientIso q).hom).app d x)
  have ht : stdSimplex.objEquiv t = SimplexCategory.const d.unop ⦋0⦌ 0 :=
    Subsingleton.elim _ _
  rw [ht]
  have hm : F.map (weakStringZeroAmbientIso q).hom ≫
      F.map (weakStringConstantExact q d.unop) =
        F.map (weakStringExactMap q (SimplexCategory.const d.unop ⦋0⦌ 0)) := by
    rw [← F.map_comp, he]
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app hm d) x).symm

end SerrePositivity.KST.Fibration
