module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarPositiveFamily
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiniteColumnComposition
/-!
概要：同じ bar 列の MC 左辺を、元の有限個の面・prefix 係数の境界項へ展開する。
方針：閉包含との微分可換性と、包含を通る斉次合成の展開を使う。
規約：境界項が零であることはここでは仮定も主張もしない。元の全次数 Hom を保つ。
使われ方：HA 方程式から各正次元列の MC 式を証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarBoundaryTerm {M : ModuleCategory R D} (s : dgCoherentBarIndex I)
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))).X 1) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X 2 :=
  let A : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X 2 :=
    (eHomWhiskerLeft (Complex R) M (Sigma.ι (dgCoherentBarFamily R D F) s)).f 2
      ((moduleHom R D (ForgetEnrichment.to (Complex R) M)
        (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))).d 1 2 f)
  let B : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).X 2 :=
    compose R (x := ForgetEnrichment.to (Complex R) M)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F s))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarColumn R D F s) f (show (1 : ℤ) + 1 = 2 from rfl)
  A + B

lemma dgCoherentBarFiniteBoundary {J : Type w} [Fintype J] {M : ModuleCategory R D}
    (s : J → dgCoherentBarIndex I) (c : J → ℤˣ)
    (f : ∀ j, (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F (s j)))).X 1) :
    (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d 1 2
        (∑ j, c j • (eHomWhiskerLeft (Complex R) M
          (Sigma.ι (dgCoherentBarFamily R D F) (s j))).f 1 (f j)) +
      compose R (x := ForgetEnrichment.to (Complex R) M)
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarTheta R D F)
        (∑ j, c j • (eHomWhiskerLeft (Complex R) M
          (Sigma.ι (dgCoherentBarFamily R D F) (s j))).f 1 (f j))
        (show (1 : ℤ) + 1 = 2 from rfl) =
      ∑ j, c j • dgCoherentBarBoundaryTerm R D F (s j) (f j) := by
  have hd := dgModuleFiniteColumn_d R D (M := M) (T := dgCoherentBarGraded R D F)
    (fun j => dgCoherentBarFamily R D F (s j))
    (fun j => Sigma.ι (dgCoherentBarFamily R D F) (s j)) c f
  change (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d 1 2
      (∑ j, c j • (eHomWhiskerLeft (Complex R) M
        (Sigma.ι (dgCoherentBarFamily R D F) (s j))).f 1 (f j)) =
    ∑ j, c j • (eHomWhiskerLeft (Complex R) M
      (Sigma.ι (dgCoherentBarFamily R D F) (s j))).f 2
        ((moduleHom R D (ForgetEnrichment.to (Complex R) M)
          (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F (s j)))).d 1 2 (f j)) at hd
  rw [hd]
  rw [dgModuleFiniteColumn_compose R D (M := M) (T := dgCoherentBarGraded R D F)
    (U := dgCoherentBarGraded R D F) (fun j => dgCoherentBarFamily R D F (s j))
    (fun j => Sigma.ι (dgCoherentBarFamily R D F) (s j)) c f (dgCoherentBarTheta R D F)
    (show (1 : ℤ) + 1 = 2 from rfl)]
  simp only [dgCoherentBarTheta_restrict, dgCoherentBarBoundaryTerm,
    smul_add, Finset.sum_add_distrib]

lemma dgCoherentBarColumn_positive_boundary {n : ℕ} (s : I _⦋n + 1⦌) :
    (moduleHom R D
      (ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩))
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))).d 1 2
        (dgCoherentBarColumn R D F ⟨n + 1, s⟩) +
      compose R (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, s⟩))
        (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
        (dgCoherentBarTheta R D F) (dgCoherentBarColumn R D F ⟨n + 1, s⟩)
        (show (1 : ℤ) + 1 = 2 from rfl) =
      ∑ j : dgCoherentBarPositiveIndex n, dgCoherentBarPositiveSign n j •
        dgCoherentBarBoundaryTerm R D F (dgCoherentBarPositiveTarget s j)
          (dgCoherentBarPositiveCoefficient R D F s j) := by
  rw [dgCoherentBarColumn_positive_coefficients R D F s]
  exact dgCoherentBarFiniteBoundary R D F (dgCoherentBarPositiveTarget s)
    (dgCoherentBarPositiveSign n) (dgCoherentBarPositiveCoefficient R D F s)

end SerrePositivity.InfinityCategories
