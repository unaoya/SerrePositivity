module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovKernel
public import Mathlib.Algebra.Homology.SingleHomology

/-!
概要：隣接切断の標準層と実 kernel のホモロジーを、元の dg 代数の H⁻⁽ⁿ⁺¹⁾ に同定する。
方針：元の商射・包含・kernel 比較のホモロジー同型を合成する。
規約：層との準同型と kernel 自体の平方零性を区別。使われ方：Postnikov 拡大の係数。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra

variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)

def postnikovLayerHomologyIso :
    (postnikovLayer R B n).homology (-(n + 1)) ≅ B.X.homology (-(n + 1)) := by
  have := postnikovLayerInclusion_quasiIsoAt R B n
  have : QuasiIsoAt (B.X.πTruncGE (-(n + 1))) (-(n + 1)) :=
    CochainComplex.quasiIsoAt_πTruncGE _ _ _ le_rfl
  exact asIso (homologyMap (postnikovLayerInclusion R B n) (-(n + 1))) ≪≫
    (asIso (homologyMap (B.X.πTruncGE (-(n + 1))) (-(n + 1)))).symm

lemma postnikovLayerHomologyIso_projection :
    (postnikovLayerHomologyIso R B n).hom ≫
      homologyMap (B.X.πTruncGE (-(n + 1))) (-(n + 1)) =
        homologyMap (postnikovLayerInclusion R B n) (-(n + 1)) := by
  simp [postnikovLayerHomologyIso]

def postnikovKernelHomologyIso :
    (postnikovKernel R B n).homology (-(n + 1)) ≅ B.X.homology (-(n + 1)) := by
  have := postnikovLayerToKernel_quasiIso R B n
  exact (asIso (homologyMap (postnikovLayerToKernel R B n) (-(n + 1)))).symm ≪≫
    postnikovLayerHomologyIso R B n

lemma postnikovLayer_exists_iso_originalHomology :
    Nonempty (postnikovLayer R B n ≅
      (single (ModuleCat R) (ComplexShape.up ℤ) (-(n + 1))).obj
        (B.X.homology (-(n + 1)))) := by
  obtain ⟨M, ⟨e⟩⟩ := postnikovLayer_exists_iso_single R B n
  let hM := (homologyFunctor (ModuleCat R) (ComplexShape.up ℤ) (-(n + 1))).mapIso e ≪≫
    singleObjHomologySelfIso (ComplexShape.up ℤ) (-(n + 1)) M
  exact ⟨e ≪≫ (single (ModuleCat R) (ComplexShape.up ℤ) (-(n + 1))).mapIso
    (hM.symm ≪≫ postnikovLayerHomologyIso R B n)⟩

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
