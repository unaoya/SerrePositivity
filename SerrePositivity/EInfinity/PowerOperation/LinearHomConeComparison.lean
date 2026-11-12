module

public import SerrePositivity.EInfinity.PowerOperation.LinearHomConeDegrees
public import SerrePositivity.EInfinity.PowerOperation.ModuleConeCoordinates

/-!
# 全 Hom と同じ指定 cone の複体同型

DAG XIII Construction 2.2.6 の完全入力の係数模型比較に用いる補助。
指定された二つの射影と全 Hom 微分の公式を通して、複体そのものを同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex
variable (R : Type w) [CommRing R] {C : Type u} [Category.{v} C] [Preadditive C]
  [HasBinaryBiproducts C] [Linear R C]
variable (P : CochainComplex C ℤ) {M N : CochainComplex C ℤ} (f : M ⟶ N)

/-- 同じ Hom-cone の次数ごとの指定同型。 -/
def linearHomConeDegreeIso (n : ℤ) :
    (mappingCone (linearHomComplexPostcompose R P f)).X n ≅
      (linearHomComplex R P (mappingCone f)).X n :=
  moduleConePairIso (linearHomComplexPostcompose R P f) n ≪≫
    (linearHomConeDegreeEquiv R P f n).symm.toModuleIso

lemma linearHomConeDegreeIso_coordinates (n : ℤ)
    (x : (mappingCone (linearHomComplexPostcompose R P f)).X n) :
    linearHomConeDegreeEquiv R P f n ((linearHomConeDegreeIso R P f n).hom x) =
      (moduleConePairIso (linearHomComplexPostcompose R P f) n).hom x := by
  change (linearHomConeDegreeEquiv R P f n)
    ((linearHomConeDegreeEquiv R P f n).symm
      ((moduleConePairIso (linearHomComplexPostcompose R P f) n).hom x)) = _
  exact (linearHomConeDegreeEquiv R P f n).apply_symm_apply _

/-- 全 Hom と同じ cone は、元の指定分解を保つ複体同型。 -/
def linearHomConeIso :
    mappingCone (linearHomComplexPostcompose R P f) ≅ linearHomComplex R P (mappingCone f) :=
  HomologicalComplex.Hom.isoOfComponents (linearHomConeDegreeIso R P f) (by
    intro n m h
    change n + 1 = m at h
    subst m
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (linearHomConeDegreeEquiv R P f (n + 1)).injective
    change linearHomConeDegreeEquiv R P f (n + 1)
        (δ n (n + 1) ((linearHomConeDegreeIso R P f n).hom x)) =
      linearHomConeDegreeEquiv R P f (n + 1)
        ((linearHomConeDegreeIso R P f (n + 1)).hom
          ((mappingCone (linearHomComplexPostcompose R P f)).d n (n + 1) x))
    rw [linearHomConeDegreeEquiv_d, linearHomConeDegreeIso_coordinates,
      linearHomConeDegreeIso_coordinates]
    have hcoord := moduleConePairIso_d (linearHomComplexPostcompose R P f) n
      ((moduleConePairIso (linearHomComplexPostcompose R P f) n).hom x)
    simp only [Iso.hom_inv_id_apply] at hcoord
    rw [hcoord]
    apply Prod.ext
    · rfl
    · exact add_comm _ _)

end SerrePositivity.EInfinity.PowerOperation
