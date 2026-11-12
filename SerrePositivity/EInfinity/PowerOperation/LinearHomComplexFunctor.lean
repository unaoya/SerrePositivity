module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex

/-!
# 線形圏の Hom 複体の後合成関手

DAG XIII Construction 2.2.6 の周期係数解像度と入力複体の比較に用いる補助。
加群の圏に限らず、表現の線形圏にも同じ Hom 微分と全後合成を適用する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex HomComplex
variable (R : Type w) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- 線形圏の Hom 複体における指定鎖写像の後合成。 -/
def linearHomComplexPostcompose (P : CochainComplex C ℤ)
    {Q T : CochainComplex C ℤ} (f : Q ⟶ T) :
    linearHomComplex R P Q ⟶ linearHomComplex R P T where
  f n := ModuleCat.ofHom
    { toFun z := z.comp (Cochain.ofHom f) (add_zero n)
      map_add' z z' := Cochain.add_comp z z' _ _
      map_smul' a z := Cochain.smul_comp a z _ _ }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_comp_ofHom z f m

/-- 表現の圏にも使える、固定解像度からの全 Hom 関手。 -/
def linearHomComplexFunctor (P : CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex (ModuleCat R) ℤ where
  obj Q := linearHomComplex R P Q
  map f := linearHomComplexPostcompose R P f
  map_id Q := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact Cochain.comp_id z
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro p q hpq
    simp [linearHomComplexPostcompose, Cochain.comp_zero_cochain_v]

end SerrePositivity.EInfinity.PowerOperation
