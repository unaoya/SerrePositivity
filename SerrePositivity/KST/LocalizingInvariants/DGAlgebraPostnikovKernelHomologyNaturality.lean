module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovLayerMaps

/-!
概要：元の Postnikov kernel のホモロジー同型は、元の代数射の H⁻⁽ⁿ⁺¹⁾ 射を保つ。
方針：標準層の準同型と元の包含の自然性を、元の kernel 同型へ移す。
規約：同型の選択を変えない。使われ方：底変更した kernel 射と元の π₂ 射の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R]

lemma postnikovLayerToKernel_homologyIso (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ) :
    homologyMap (postnikovLayerToKernel R B n) (-(n + 1)) ≫
      (postnikovKernelHomologyIso R B n).hom = (postnikovLayerHomologyIso R B n).hom := by
  have := postnikovLayerToKernel_quasiIso R B n
  change homologyMap (postnikovLayerToKernel R B n) (-(n + 1)) ≫
    (inv (homologyMap (postnikovLayerToKernel R B n) (-(n + 1))) ≫ _) = _
  rw [IsIso.hom_inv_id_assoc]

variable {B C : Mon (Complex R)} [B.X.IsStrictlyLE 0] [C.X.IsStrictlyLE 0] (f : B ⟶ C) (n : ℤ)

lemma postnikovKernelHomologyIso_naturality :
    homologyMap (postnikovKernelMap R f n) (-(n + 1)) ≫
      (postnikovKernelHomologyIso R C n).hom =
        (postnikovKernelHomologyIso R B n).hom ≫ homologyMap f.hom (-(n + 1)) := by
  have := postnikovLayerToKernel_quasiIso R B n
  apply (cancel_epi (homologyMap (postnikovLayerToKernel R B n) (-(n + 1)))).1
  calc
    _ = homologyMap (postnikovLayerMap R f n) (-(n + 1)) ≫
        (homologyMap (postnikovLayerToKernel R C n) (-(n + 1)) ≫
          (postnikovKernelHomologyIso R C n).hom) := by
      rw [← Category.assoc, ← homologyMap_comp, ← postnikovLayerToKernel_naturality,
        homologyMap_comp, Category.assoc]
    _ = homologyMap (postnikovLayerMap R f n) (-(n + 1)) ≫
        (postnikovLayerHomologyIso R C n).hom := by rw [postnikovLayerToKernel_homologyIso]
    _ = (postnikovLayerHomologyIso R B n).hom ≫ homologyMap f.hom (-(n + 1)) :=
      postnikovLayerHomologyIso_naturality R f n
    _ = _ := by rw [← Category.assoc, postnikovLayerToKernel_homologyIso]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
