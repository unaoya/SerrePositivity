module

public import SerrePositivity.EInfinity.PowerOperation.LinearHomComplexFunctor

/-!
# 指定解像度の射による全 Hom 関手の前合成

DAG XIII Construction 2.2.6 の周期解像度の正の部分への制限に用いる補助。
同じ指定解像度の射による前合成を、全係数複体に自然な鎖写像として作る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CochainComplex HomComplex
variable (R : Type w) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]

/-- 同じ指定解像度の射による線形 Hom 複体の前合成。 -/
def linearHomComplexPrecompose {P Q : CochainComplex C ℤ} (f : P ⟶ Q)
    (M : CochainComplex C ℤ) : linearHomComplex R Q M ⟶ linearHomComplex R P M where
  f n := ModuleCat.ofHom
    { toFun z := (Cochain.ofHom f).comp z (zero_add n)
      map_add' z z' := Cochain.comp_add _ z z' _
      map_smul' a z := Cochain.comp_smul _ a z _ }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_ofHom_comp f z m

/-- 前合成は、全係数複体と全鎖写像について自然。 -/
def linearHomComplexPrecomposition {P Q : CochainComplex C ℤ} (f : P ⟶ Q) :
    linearHomComplexFunctor R Q ⟶ linearHomComplexFunctor R P where
  app M := linearHomComplexPrecompose R f M
  naturality M N g := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Cochain.ext
    intro i j hij
    simp [linearHomComplexFunctor, linearHomComplexPrecompose, linearHomComplexPostcompose,
      Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v]

end SerrePositivity.EInfinity.PowerOperation
