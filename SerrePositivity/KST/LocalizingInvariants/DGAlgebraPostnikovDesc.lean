module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovMap

/-!
概要：下に有界な実 dg 代数への射の、一意な有限 Postnikov 降下を構成する。
方針：複体の降下の単位・積保存を元の射影の tensor 全射性で証明する。
規約：商の普遍性は代数射の等式として保持。使われ方：Postnikov の遷移射。
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

variable (R : Type u) [CommRing R] {B C : Mon (Complex R)} [B.X.IsStrictlyLE 0]
  (n : ℤ) [C.X.IsStrictlyGE (-n)]

def postnikovDesc (f : B ⟶ C) : postnikov R B n ⟶ C := by
  let t := TruncationDesc.descend (-n) f.hom
  have ht : B.X.πTruncGE (-n) ≫ t = f.hom := TruncationDesc.projection_descend _ _
  refine Mon.Hom.mk' t ?_ ?_
  · change (η[B.X] ≫ B.X.πTruncGE (-n)) ≫ t = η[C.X]
    rw [Category.assoc, ht, IsMonHom.one_hom]
  · have := TruncationDesc.tensor_epi (B.X.πTruncGE (-n)) (B.X.πTruncGE (-n))
    apply (cancel_epi (B.X.πTruncGE (-n) ⊗ₘ B.X.πTruncGE (-n))).1
    change (B.X.πTruncGE (-n) ⊗ₘ B.X.πTruncGE (-n)) ≫
      (postnikovMul R B n ≫ t) =
      (B.X.πTruncGE (-n) ⊗ₘ B.X.πTruncGE (-n)) ≫ ((t ⊗ₘ t) ≫ μ[C.X])
    rw [← Category.assoc, postnikovMul_projection, Category.assoc, ht]
    rw [tensorHom_comp_tensorHom_assoc, ht, IsMonHom.mul_hom]

lemma postnikovQuotient_desc (f : B ⟶ C) :
    postnikovQuotient R B n ≫ postnikovDesc R n f = f := by
  apply Mon.Hom.ext
  exact TruncationDesc.projection_descend _ _

lemma postnikovDesc_unique (f : B ⟶ C) (g : postnikov R B n ⟶ C)
    (hg : postnikovQuotient R B n ≫ g = f) : g = postnikovDesc R n f := by
  apply Mon.Hom.ext
  apply (cancel_epi (B.X.πTruncGE (-n))).1
  change (postnikovQuotient R B n ≫ g).hom =
    (postnikovQuotient R B n ≫ postnikovDesc R n f).hom
  rw [hg, postnikovQuotient_desc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
