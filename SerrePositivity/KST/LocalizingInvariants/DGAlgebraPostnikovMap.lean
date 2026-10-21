module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikov

/-!
概要：有限 Postnikov 切断の元の chain map が、単位と非可換積を保存することを示す。
方針：射影およびその tensor の全射性で消去し、元の代数射と自然性へ戻す。
規約：追加の積保存性を入力しない。使われ方：代数 Postnikov 塔の関手性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R] {B C : Mon (Complex R)}
  [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0]

def postnikovMap (f : B ⟶ C) (n : ℤ) : postnikov R B n ⟶ postnikov R C n := by
  let t := CochainComplex.truncGEMap f.hom (-n)
  have ht : B.X.πTruncGE (-n) ≫ t = f.hom ≫ C.X.πTruncGE (-n) :=
    CochainComplex.πTruncGE_naturality f.hom (-n)
  refine Mon.Hom.mk' t ?_ ?_
  · change (η[B.X] ≫ B.X.πTruncGE (-n)) ≫ t = η[C.X] ≫ C.X.πTruncGE (-n)
    rw [Category.assoc, ht, ← Category.assoc, IsMonHom.one_hom]
  · have := TruncationDesc.tensor_epi (B.X.πTruncGE (-n)) (B.X.πTruncGE (-n))
    apply (cancel_epi (B.X.πTruncGE (-n) ⊗ₘ B.X.πTruncGE (-n))).1
    change (B.X.πTruncGE (-n) ⊗ₘ B.X.πTruncGE (-n)) ≫
      (postnikovMul R B n ≫ t) =
      (B.X.πTruncGE (-n) ⊗ₘ B.X.πTruncGE (-n)) ≫
        ((t ⊗ₘ t) ≫ postnikovMul R C n)
    rw [← Category.assoc, postnikovMul_projection, Category.assoc, ht]
    simp only [tensorHom_comp_tensorHom_assoc, ht]
    rw [← tensorHom_comp_tensorHom_assoc, postnikovMul_projection,
      ← Category.assoc, IsMonHom.mul_hom, Category.assoc]

lemma postnikovMap_hom (f : B ⟶ C) (n : ℤ) :
    (postnikovMap R f n).hom = (postnikovComplex R n).map f := rfl

lemma postnikovQuotient_naturality (f : B ⟶ C) (n : ℤ) :
    postnikovQuotient R B n ≫ postnikovMap R f n = f ≫ postnikovQuotient R C n := by
  apply Mon.Hom.ext
  exact CochainComplex.πTruncGE_naturality f.hom (-n)

lemma postnikovMap_quasiIso_iff (f : B ⟶ C) (n : ℤ) :
    QuasiIso (postnikovMap R f n).hom ↔
      ∀ j : ℤ, j ≤ n → Function.Bijective ((groups R j).map f).hom :=
  postnikovComplex_map_quasiIso_iff R f n

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
