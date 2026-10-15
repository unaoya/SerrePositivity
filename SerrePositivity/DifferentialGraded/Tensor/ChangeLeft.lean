module
public import SerrePositivity.DifferentialGraded.Tensor.Balanced

/-! # 等しい左加群によるbalanced tensorの対象表示の変更 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群の等式でbalanced tensorを運ぶ標準同型。 -/
def changeLeft (M : RightModule A D) {N N' : LeftModule A D} (h : N = N') :
    obj A D M N ≅ obj A D M N' := eqToIso (congrArg (obj A D M) h)

@[reassoc]
lemma ι_changeLeft_hom (M : RightModule A D) {N N' : LeftModule A D} (h : N = N') (x : D) :
    ι A D M N x ≫ (changeLeft A D M h).hom =
      eqToHom (congrArg (fun L : LeftModule A D => M.obj (op x) ⊗ L.obj x) h) ≫ ι A D M N' x := by
  subst N'
  simp only [changeLeft, eqToIso_refl, Iso.refl_hom, Category.comp_id, eqToHom_refl,
    Category.id_comp]

end SerrePositivity.DifferentialGraded.BalancedTensor
