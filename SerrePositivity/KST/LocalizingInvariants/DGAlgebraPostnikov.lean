module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovComplex
public import SerrePositivity.KST.LocalizingInvariants.CochainTensorTruncationDesc
public import SerrePositivity.KST.LocalizingInvariants.MonoidObjectAlongEpi

/-!
概要：厳密な非正次数 dg 代数の smart τ≥−n を、実非可換 dg 代数として構成する。
方針：内部 Hom の下界から積を二変数で降ろし、tensor 全射で代数則を証明する。
規約：underlying complex と射影は既存 Postnikov 模型そのもの。使われ方：pro 切除。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex ComplexShape
open scoped MonObj
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)

instance postnikovComplex_lowerBound : ((postnikovComplex R n).obj B).IsStrictlyGE (-n) := by
  change (HomologicalComplex.truncGE B.X (embeddingUpIntGE (-n))).IsStrictlySupported _
  infer_instance

instance postnikovComplex_nonpositive : ((postnikovComplex R n).obj B).IsStrictlyLE 0 :=
  TruncationDesc.truncation_nonpositive B.X (-n)

def postnikovMul :
    (postnikovComplex R n).obj B ⊗ (postnikovComplex R n).obj B ⟶
      (postnikovComplex R n).obj B := by
  change B.X.truncGE (-n) ⊗ B.X.truncGE (-n) ⟶ B.X.truncGE (-n)
  have : (B.X.truncGE (-n)).IsStrictlyGE (-n) :=
    postnikovComplex_lowerBound R B n
  exact TruncationDesc.descendTensor (-n) (μ[B.X] ≫ B.X.πTruncGE (-n))

lemma postnikovMul_projection :
    (B.X.πTruncGE (-n) ⊗ₘ B.X.πTruncGE (-n)) ≫ postnikovMul R B n =
      μ[B.X] ≫ B.X.πTruncGE (-n) :=
  TruncationDesc.projection_descendTensor (-n) _

/-- 元の射影と積の降下から得る有限 Postnikov dg 代数。 -/
def postnikov : Mon (Complex R) := by
  let p := B.X.πTruncGE (-n)
  have : Epi p := TruncationDesc.projection_epi B.X (-n)
  have : Epi (𝟙_ (Complex R) ◁ p) := by
    rw [← id_tensorHom]
    exact TruncationDesc.tensor_epi _ _
  have : Epi (p ▷ 𝟙_ (Complex R)) := by
    rw [← tensorHom_id]
    exact TruncationDesc.tensor_epi _ _
  have : Epi (p ⊗ₘ p) := TruncationDesc.tensor_epi _ _
  have : Epi ((p ⊗ₘ p) ⊗ₘ p) := TruncationDesc.tensor_epi _ _
  exact { X := (postnikovComplex R n).obj B
          mon := monoidObjectAlongEpi B p (postnikovMul R B n)
            (postnikovMul_projection R B n) }

def postnikovQuotient : B ⟶ postnikov R B n :=
  Mon.Hom.mk' (B.X.πTruncGE (-n)) rfl (postnikovMul_projection R B n).symm

lemma postnikov_underlying : (postnikov R B n).X = (postnikovComplex R n).obj B := rfl

lemma postnikovQuotient_hom : (postnikovQuotient R B n).hom =
    (postnikovProjection R n).app B := rfl

lemma postnikov_isConnective : IsConnective R (postnikov R B n) := by
  change ((postnikovComplex R n).obj B).IsLE 0
  infer_instance

lemma postnikovQuotient_groups_isIso (j : ℤ) (hj : j ≤ n) :
    IsIso ((groups R j).map (postnikovQuotient R B n)) :=
  postnikovProjection_groups_isIso R B n j hj

lemma postnikov_groups_subsingleton (j : ℤ) (hj : n < j) :
    Subsingleton ((groups R j).obj (postnikov R B n)) :=
  postnikovComplex_groups_subsingleton R B n j hj

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
