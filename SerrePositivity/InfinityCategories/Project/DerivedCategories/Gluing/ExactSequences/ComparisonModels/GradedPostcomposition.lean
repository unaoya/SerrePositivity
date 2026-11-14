module
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison
public import SerrePositivity.DifferentialGraded.Module.Graded
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! 任意 dg 圏の全次数の後合成、その Yoneda 評価、および実 dg 関手との整合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E]

/-- 実豊穣合成の転置としての全次数の後合成。圏の Small 性は不要。 -/
def dgGluingGradedPostcomposition (x y z : E) : homObject R E y z ⟶
    homComplex R (homObject R E x y) (homObject R E x z) :=
  curryRight ((β_ (homObject R E y z) (homObject R E x y)).hom ≫ eComp (Complex R) x y z)

/-- 斉次射の作用は、符号を含む元の通常順の合成そのもの。 -/
lemma dgGluingGradedPostcomposition_apply (x y z : E) {p q n : ℤ}
    (g : GradedHom R y z p) (b : GradedHom R x y q) (hn : q + p = n) :
    (((dgGluingGradedPostcomposition R E x y z).f p g).v q n hn) b =
      compose R (x := x) (y := y) (z := z) g b hn := by
  change (eComp (Complex R) x y z).f n
    ((signedSwap (homObject R E y z) (homObject R E x y)).hom.f n
      (ιTensorObj (homObject R E y z) (homObject R E x y) p q n (by omega) (g ⊗ₜ[R] b))) = _
  rw [signedSwap_apply]
  simp only [Units.smul_def, map_zsmul]
  change (p * q).negOnePow • forward R (x := x) (y := y) (z := z) b g hn = _
  rw [compose, mul_comm p q]

/-- 全 Yoneda Hom の評価は、同じ全次数の後合成の cochain と一致。 -/
lemma dgGluingYonedaHom_postcomposition [Small.{u} E] (x y z : E) {p : ℤ}
    (g : GradedHom R y z p) :
    (moduleHomπ R E (representable R y) (representable R z) x).f p
      ((yonedaHom R E y z).f p g) =
    (dgGluingGradedPostcomposition R E x y z).f p g := by
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  rw [yonedaHom_element, dgGluingGradedPostcomposition_apply, compose, mul_comm p q]

/-- 全次数の後合成は、任意の実 dg 関手の Hom 鎖写像と厳密に可換する。 -/
lemma dgGluingGradedPostcomposition_naturality (C : Type w) [DGCategory R C]
    (F : DGFunctor R E C) (x y z : E) {p : ℤ} (g : GradedHom R y z p) :
    ((dgGluingGradedPostcomposition R E x y z).f p g).comp
      (Cochain.ofHom (F.map x z)) (add_zero p) =
    (Cochain.ofHom (F.map x y)).comp
      ((dgGluingGradedPostcomposition R C (F.obj x) (F.obj y) (F.obj z)).f p
        ((F.map y z).f p g)) (zero_add p) := by
  apply Cochain.ext
  intro q n hn
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    ModuleCat.comp_apply]
  rw [dgGluingGradedPostcomposition_apply, dgGluingGradedPostcomposition_apply]
  unfold compose
  simp only [Units.smul_def, map_zsmul]
  rw [F.map_forward R]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
