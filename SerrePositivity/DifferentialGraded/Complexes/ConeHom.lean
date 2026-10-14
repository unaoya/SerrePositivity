module
public import SerrePositivity.DifferentialGraded.Complexes.Cone

/-! # 全次数で可換する square から cone の Hom chain map -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A] {K P Q R S : Complex A}

/-- 可換 square の成分を斉次 cochain の可換式として読む。 -/
lemma coneHom_square_apply (f : P ⟶ Q) (g : R ⟶ S)
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S)
    (h : a ≫ homPostcompose P g = b ≫ homPrecompose f S) (p : ℤ) (t : K.X p) :
    (a.f p t).comp (Cochain.ofHom g) (add_zero p) =
      (Cochain.ofHom f).comp (b.f p t) (zero_add p) :=
  congrArg (fun l => l.f p t) h

/-- 可換 square の Hom chain map を cone の Hom chain map にする。 -/
def coneHomMap (f : P ⟶ Q) (g : R ⟶ S)
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S)
    (h : a ≫ homPostcompose P g = b ≫ homPrecompose f S) :
    K ⟶ homComplex A (mappingCone f) (mappingCone g) where
  f p := ModuleCat.ofHom
    { toFun t := coneMapCochain f g (a.f p t) (b.f p t)
      map_add' t t' := by rw [map_add, map_add, coneMapCochain_add]
      map_smul' r t := by
        rw [map_smul, map_smul, coneMapCochain_smul]
        rfl }
  comm' p q hpq := by
    obtain rfl : q = p + 1 := hpq.symm
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    change δ p (p + 1) (coneMapCochain f g (a.f p t) (b.f p t)) =
      coneMapCochain f g (a.f (p + 1) (K.d p (p + 1) t))
        (b.f (p + 1) (K.d p (p + 1) t))
    rw [coneMapCochain_differential f g _ _ (coneHom_square_apply f g a b h p t)]
    have ha := congrArg (fun l : K.X p ⟶ (homComplex A P R).X (p + 1) => l t)
      (a.comm p (p + 1))
    have hb := congrArg (fun l : K.X p ⟶ (homComplex A Q S).X (p + 1) => l t)
      (b.comm p (p + 1))
    change δ p (p + 1) (a.f p t) = a.f (p + 1) (K.d p (p + 1) t) at ha
    change δ p (p + 1) (b.f p t) = b.f (p + 1) (K.d p (p + 1) t) at hb
    rw [ha, hb]

/-- cone Hom chain map の成分は符号付き対角 cochain。 -/
lemma coneHomMap_apply (f : P ⟶ Q) (g : R ⟶ S)
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S) (h)
    (p : ℤ) (t : K.X p) :
    (coneHomMap f g a b h).f p t = coneMapCochain f g (a.f p t) (b.f p t) := rfl

/-- cone の標準包含の全次数 Hom 自然性。 -/
lemma coneHomMap_inr (f : P ⟶ Q) (g : R ⟶ S)
    (a : K ⟶ homComplex A P R) (b : K ⟶ homComplex A Q S) (h) :
    b ≫ homPostcompose Q (mappingCone.inr g) =
      coneHomMap f g a b h ≫ homPrecompose (mappingCone.inr f) (mappingCone g) := by
  apply HomologicalComplex.Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  exact (coneMapCochain_inr f g (a.f p t) (b.f p t)).symm
end SerrePositivity.DifferentialGraded
