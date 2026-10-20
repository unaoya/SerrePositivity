module
public import SerrePositivity.KST.SConstruction.TensorRightMultiplication

/-! # 右端の積の後の削除
概要：増大を保つ積の後の削除は、元の二因子の二回の削除と一致する。
方針：積の増大保存を結合の自然性へ移し、単位の coherence と自然性で整理する。
規約：元の結合射と因子順を保つ。使われ方：cubical connection と退化の同座標関係。
-/
@[expose] public section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
variable {V : Type u} [Category.{v} V] [MonoidalCategory V] (L P : V) [MonObj P]

/-- 増大を保つ右端の積を削除すると、元の二つの因子を順に削除した射になる。 -/
lemma tensorRightMultiplication_deletion (t : P ⟶ 𝟙_ V)
    (h : MonObj.mul ≫ t = (t ⊗ₘ t) ≫ (λ_ (𝟙_ V)).hom) :
    tensorRightMultiplication L P ≫ (L ◁ t) ≫ (ρ_ L).hom =
      ((L ⊗ P) ◁ t) ≫ (ρ_ (L ⊗ P)).hom ≫ (L ◁ t) ≫ (ρ_ L).hom := by
  dsimp only [tensorRightMultiplication]
  simp only [Category.assoc]
  rw [← whiskerLeft_comp_assoc, h]
  simp only [tensorHom_def', whiskerLeft_comp, Category.assoc]
  rw [← associator_naturality_right_assoc, ← associator_naturality_middle_assoc]
  have hc : (α_ L (𝟙_ V) (𝟙_ V)).hom ≫ (L ◁ (λ_ (𝟙_ V)).hom) =
      (ρ_ (L ⊗ 𝟙_ V)).hom := by monoidal
  slice_lhs 3 4 => rw [hc]
  rw [rightUnitor_naturality_assoc]

end SerrePositivity.KST.SConstruction
