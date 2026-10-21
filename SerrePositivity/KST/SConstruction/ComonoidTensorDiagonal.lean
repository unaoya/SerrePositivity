module
public import Mathlib.CategoryTheory.Monoidal.Comon_

/-! # 余モノイド射の tensor 対角の回収
概要：tensor からの余モノイド射の対角保存を、中央因子の交換を明示して書く。
方針：元の tensor 余モノイドの対角の式に、元の余モノイド射の法則を適用する。
規約：因子の順序を保持。使われ方：Λ の Serre 対角の合成保存。
-/
@[expose] public section
universe v u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open scoped ComonObj
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- 元の tensor 余モノイドからの射は、元の中央二因子の交換を含む対角を保つ。 -/
lemma comonoidTensorDiagonal {P Q R : Comon C} (f : P ⊗ Q ⟶ R) :
    f.hom ≫ Δ[R.X] = (Δ[P.X] ⊗ₘ Δ[Q.X]) ≫
      tensorμ P.X P.X Q.X Q.X ≫ (f.hom ⊗ₘ f.hom) := by
  have h := f.isComonHom_hom.hom_comul
  change f.hom ≫ Δ[R.X] = Δ[P.X ⊗ Q.X] ≫ (f.hom ⊗ₘ f.hom) at h
  rw [Comon.tensorObj_comul, Category.assoc] at h
  exact h

omit [BraidedCategory C] in
/-- 元の余モノイド射を前合成すると、同じ二つの出力への対角を回収する。 -/
lemma comonoidPair_precompose {P Q : Comon C} {X Y : C}
    (f : P ⟶ Q) (a : Q.X ⟶ X) (b : Q.X ⟶ Y) :
    f.hom ≫ Δ[Q.X] ≫ (a ⊗ₘ b) = Δ[P.X] ≫ ((f.hom ≫ a) ⊗ₘ (f.hom ≫ b)) := by
  rw [← Category.assoc, IsComonHom.hom_comul, Category.assoc,
    tensorHom_comp_tensorHom]

omit [BraidedCategory C] in
/-- 元の対角の三因子への二回適用は、元の結合同型と両立する。 -/
lemma comonoidDiagonal_associativity (P : Comon C) :
    (Δ[P.X] ≫ (Δ[P.X] ⊗ₘ 𝟙 P.X)) ≫ (α_ P.X P.X P.X).hom =
      Δ[P.X] ≫ (𝟙 P.X ⊗ₘ Δ[P.X]) := by
  rw [tensorHom_id, id_tensorHom, Category.assoc]
  exact (ComonObj.comul_assoc P.X).symm

/-- 元の tensor 余モノイドからの射は、元の二つの増大を保つ。 -/
lemma comonoidTensorCounit {P Q R : Comon C} (f : P ⊗ Q ⟶ R) :
    f.hom ≫ ε[R.X] = (ε[P.X] ⊗ₘ ε[Q.X]) ≫ (λ_ (𝟙_ C)).hom := by
  have h := f.isComonHom_hom.hom_counit
  change f.hom ≫ ε[R.X] = ε[P.X ⊗ Q.X] at h
  exact h.trans (Comon.tensorObj_counit P.X Q.X)

omit [BraidedCategory C] in
/-- 元の対角と左の増大の合成は、元の左単位で恒等へ戻る。 -/
lemma comonoidDiagonal_left_counit (P : Comon C) :
    (Δ[P.X] ≫ (ε[P.X] ⊗ₘ 𝟙 P.X)) ≫ (λ_ P.X).hom = 𝟙 P.X := by
  rw [tensorHom_id, ComonObj.counit_comul, Iso.inv_hom_id]

omit [BraidedCategory C] in
/-- 元の対角と右の増大の合成は、元の右単位で恒等へ戻る。 -/
lemma comonoidDiagonal_right_counit (P : Comon C) :
    (Δ[P.X] ≫ (𝟙 P.X ⊗ₘ ε[P.X])) ≫ (ρ_ P.X).hom = 𝟙 P.X := by
  rw [id_tensorHom, ComonObj.comul_counit, Iso.inv_hom_id]

end SerrePositivity.KST.SConstruction
