module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSimplexConstant

/-!
概要：実乗法的写像模型の零単体は元の代数射に全単射で対応する。
方針：元の AW 零単体の定数代数同型を後合成し、実逆射で戻す。
規約：元の代数射と指定底を保持し、π₀ の比較とは区別する。
使われ方：導来写像空間比較の零単体での元の射の正規化。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R))

def multiplicativeMappingVertexEquiv :
    (A ⟶ B) ≃ (multiplicativeMappingSimplices R A B) _⦋0⦌ := by
  letI := simplexConstant_zero_isIso R B
  change (A ⟶ B) ≃ (A ⟶ (convolutionFunctor R (simplexComonoid R ⦋0⦌)).obj B)
  exact {
    toFun f := f ≫ convolutionConstantMap R (simplexComonoid R ⦋0⦌) B
    invFun a := a ≫ inv (convolutionConstantMap R (simplexComonoid R ⦋0⦌) B)
    left_inv f := by
      change (f ≫ convolutionConstantMap R (simplexComonoid R ⦋0⦌) B) ≫
        inv (convolutionConstantMap R (simplexComonoid R ⦋0⦌) B) = f
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    right_inv a := by
      change A ⟶ (convolutionFunctor R (simplexComonoid R ⦋0⦌)).obj B at a
      change (a ≫ inv (convolutionConstantMap R (simplexComonoid R ⦋0⦌) B)) ≫
        convolutionConstantMap R (simplexComonoid R ⦋0⦌) B = a
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id] }

lemma multiplicativeMappingVertexEquiv_apply (f : A ⟶ B) :
    multiplicativeMappingVertexEquiv R A B f = multiplicativeMappingBasePoint R f := rfl

lemma multiplicativeMappingVertexEquiv_precompose {A' : Mon (Complex R)}
    (f : A' ⟶ A) (g : A ⟶ B) :
    (multiplicativeMappingPrecompose R f B).app (op ⦋0⦌)
      (multiplicativeMappingVertexEquiv R A B g) =
        multiplicativeMappingVertexEquiv R A' B (f ≫ g) := by
  change f ≫ (g ≫ convolutionConstantMap R (simplexComonoid R ⦋0⦌) B) =
    (f ≫ g) ≫ convolutionConstantMap R (simplexComonoid R ⦋0⦌) B
  exact (Category.assoc _ _ _).symm

lemma multiplicativeMappingVertexEquiv_postcompose {C : Mon (Complex R)}
    (f : A ⟶ B) (q : B ⟶ C) :
    (multiplicativeMappingPostcompose R A q).app (op ⦋0⦌)
      (multiplicativeMappingVertexEquiv R A B f) =
        multiplicativeMappingVertexEquiv R A C (f ≫ q) := by
  change (f ≫ convolutionConstantMap R (simplexComonoid R ⦋0⦌) B) ≫
      (convolutionFunctor R (simplexComonoid R ⦋0⦌)).map q =
    (f ≫ q) ≫ convolutionConstantMap R (simplexComonoid R ⦋0⦌) C
  rw [Category.assoc, convolutionConstantMap_naturality, Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
