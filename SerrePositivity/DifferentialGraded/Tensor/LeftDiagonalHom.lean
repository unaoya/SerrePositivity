module
public import SerrePositivity.DifferentialGraded.Tensor.LeftDiagonalValues

/-! # 対角左制限とのYoneda評価の加群変数自然性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]

/-- 左representableの表示を等式で替えても、全Hom自然性は保たれる。 -/
lemma leftYoneda_changeLeft_enriched_naturality (M M' : RightModule A B) (b : B)
    (N : LeftModule A B) (h : N = leftRepresentable A b) :
    rightHomMap A B M M' N ≫ homPostcompose (obj A B M N)
      ((changeLeft A B M' h).hom ≫ leftYonedaEvaluation A B b M') =
    moduleHomπ A B M M' b ≫
      homPrecompose ((changeLeft A B M h).hom ≫ leftYonedaEvaluation A B b M)
        (M'.obj (op b)) := by
  subst N
  simpa only [changeLeft, eqToIso_refl, Iso.refl_hom, Category.id_comp] using
    leftYonedaEvaluation_enriched_naturality A B b M M'

lemma leftUnitValueHom_enriched_naturality (M M' : RightModule A B) (b : B) :
    rightHomMap A B M M' ((Bimodule.diagonal A B).leftAt b) ≫
      homPostcompose (obj A B M ((Bimodule.diagonal A B).leftAt b))
        (leftUnitValueHom A B M' b) =
    moduleHomπ A B M M' b ≫
      homPrecompose (leftUnitValueHom A B M b) (M'.obj (op b)) :=
  leftYoneda_changeLeft_enriched_naturality A B M M' b
    ((Bimodule.diagonal A B).leftAt b) (Bimodule.diagonal_leftAt A B b)

end SerrePositivity.DifferentialGraded.BalancedTensor
