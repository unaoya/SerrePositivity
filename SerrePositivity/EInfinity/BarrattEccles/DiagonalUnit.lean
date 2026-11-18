module

public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionDiagonal
public import SerrePositivity.EInfinity.BarrattEccles.Unit
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainVertices

/-!
# AW 対角の単位保存

概要：Berger–Fresse §1.1.4 の対角が Barratt–Eccles の単位を保存することを示す。
方針：単位複体からの射を零次の 1 で比較し、頂点の対角公式を適用する。
規約：終域の単位はテンソル単位の逆単位子に続く二つの単位射。
使われ方：Hopf 対角のオペラッド射の単位条件を満たす。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped TensorProduct

variable (A : Type u) [CommRing A]

private lemma unitLeftUnitor_inv_apply (x : (𝟙_ (Complex A)).X 0) :
    ((λ_ (𝟙_ (Complex A))).inv).f 0 x =
      ιTensorObj (𝟙_ (Complex A)) (𝟙_ (Complex A)) 0 0 0 (by omega)
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) ⊗ₜ[A] x) := by
  change (HomologicalComplex.leftUnitor' (𝟙_ (Complex A))).inv 0 x = _
  rw [HomologicalComplex.leftUnitor'_inv]
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]
  rfl

/-- 概要：AW 対角は Barratt–Eccles の単位を保存する（Berger–Fresse §1.1.4）。
方針：単位は零単体の生成元であり、AW はこれを自己テンソルへ送る。
規約：全複体の射の等式として述べる。
使われ方：Hopf 対角をテンソルオペラッドへの射へ束ねる。 -/
lemma unit_diagonal :
    unit A ≫ complexDiagonal A 1 =
      (λ_ (𝟙_ (Complex A))).inv ≫ (unit A ⊗ₘ unit A) := by
  apply from_single_hom_ext
  apply (cancel_epi (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (complexDiagonal A 1).f 0
      ((unit A).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) =
    (HomologicalComplex.tensorHom (unit A) (unit A)).f 0
      (((λ_ (𝟙_ (Complex A))).inv).f 0
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)))
  rw [unit_zero_apply, one_smul, unitLeftUnitor_inv_apply]
  rw [SerrePositivity.cochainTensorMap_apply_ι, unit_zero_apply, one_smul]
  exact _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainDiagonal_vertex A (simplicial 1) unitSimplex

end SerrePositivity.EInfinity.BarrattEccles
