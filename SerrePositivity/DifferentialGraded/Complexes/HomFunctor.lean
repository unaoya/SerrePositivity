module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-! # linearHomComplex の両変数関手性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CochainComplex HomComplex
variable {A : Type u} [CommRing A]

/-- Hom 複体の値域での後合成。次数を変えず微分と可換。 -/
def homPostcompose (P : Complex A) {Q T : Complex A} (f : Q ⟶ T) :
    homComplex A P Q ⟶ homComplex A P T where
  f n := ModuleCat.ofHom
    { toFun z := z.comp (Cochain.ofHom f) (add_zero n)
      map_add' z z' := Cochain.add_comp z z' _ _
      map_smul' a z := Cochain.smul_comp a z _ _ }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_comp_ofHom z f m

/-- Hom 複体の原変数での前合成。 -/
def homPrecompose {P Q : Complex A} (f : P ⟶ Q) (T : Complex A) :
    homComplex A Q T ⟶ homComplex A P T where
  f n := ModuleCat.ofHom
    { toFun z := (Cochain.ofHom f).comp z (zero_add n)
      map_add' z z' := Cochain.comp_add _ z z' _
      map_smul' a z := Cochain.comp_smul _ a z _ }
  comm' n m _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact δ_ofHom_comp f z m

/-- 後合成の成分公式。 -/
@[simp]
lemma homPostcompose_apply (P : Complex A) {Q T : Complex A} (f : Q ⟶ T)
    (n : ℤ) (z : Homogeneous P Q n) :
    (homPostcompose P f).f n z = z.comp (Cochain.ofHom f) (add_zero n) := rfl

/-- 前合成の成分公式。 -/
@[simp]
lemma homPrecompose_apply {P Q : Complex A} (f : P ⟶ Q) (T : Complex A)
    (n : ℤ) (z : Homogeneous Q T n) :
    (homPrecompose f T).f n z = (Cochain.ofHom f).comp z (zero_add n) := rfl

/-- 原変数を固定した A 線形 Hom 関手。 -/
def homFunctor (P : Complex A) : Complex A ⥤ Complex A where
  obj Q := homComplex A P Q
  map f := homPostcompose P f
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
    simp [homPostcompose, Cochain.comp_zero_cochain_v]
end SerrePositivity.DifferentialGraded
