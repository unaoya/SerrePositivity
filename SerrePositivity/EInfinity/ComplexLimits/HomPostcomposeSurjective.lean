module

public import SerrePositivity.EInfinity.ComplexLimits.CofibrantComponentsProjective
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex

/-!
# 射影始域からの内部 Hom の各次数での全射性

概要：各次数射影の始域からの Hom は次数別全射を次数別全射へ送る。
方針：同じ homogeneous cochain の成分を射影加群の lift で持ち上げる。
規約：次数の有界性を仮定しない。
使われ方：cofibrant 始域の内部 Hom の右 Quillen 性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

lemma homPostcompose_degreewise_surjective (P : Complex A)
    [∀ n : ℤ, Projective (P.X n)] {X Y : Complex A} (f : X ⟶ Y)
    (hf : projectiveFibrations A f) (n : ℤ) :
    Function.Surjective ((homPostcompose P f).f n) := by
  have (q : ℤ) : Epi (f.f q) := (ModuleCat.epi_iff_surjective _).mpr (hf q)
  intro z
  let w : Homogeneous P X n := Cochain.mk
    (fun p q hpq => Projective.factorThru (z.v p q hpq) (f.f q))
  refine ⟨w, ?_⟩
  rw [homPostcompose_apply]
  apply Cochain.ext
  intro p q hpq
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v, w, Cochain.mk_v,
    Projective.factorThru_comp]

lemma homPostcompose_cofibrant_fibration (P : Complex A)
    (hP : (projectiveGeneratingCofibrations A).rlp.llp
      (0 : (HomologicalComplex.zero : Complex A) ⟶ P)) {X Y : Complex A} (f : X ⟶ Y)
    (hf : projectiveFibrations A f) : projectiveFibrations A (homPostcompose P f) := by
  have (n : ℤ) := projectiveCofibrant_component_projective P hP n
  exact homPostcompose_degreewise_surjective P f hf

end SerrePositivity.EInfinity.ComplexLimits
