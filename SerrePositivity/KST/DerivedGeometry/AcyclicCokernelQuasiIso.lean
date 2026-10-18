module

public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
概要：余核複体が非輪状な短完全列の第一射は準同型。
方針：長完全列の隣接する余核コホモロジーの零性から各コホモロジー写像の単射性と全射性を得る。
規約：任意のアーベル圏の非有界複体。
使われ方：Stacks Lemma 19.12.5 (079N)、TT §3・§8、Toën §3.2 の準同型拡大。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C]

/--
概要：非輪状な余核を持つ短完全列の単射は準同型。
方針：コホモロジー長完全列を各整数次数で使う。
規約：複体の有界性を要求しない。
使われ方：Stacks Lemma 19.12.5、TT §3 の非有界準同型拡大。
-/
lemma shortExact_quasiIso_f_of_acyclic
    (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact) (h₃ : S.X₃.Acyclic) :
    QuasiIso S.f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hz₀ := (h₃ n).isZero_homology
  have hz₁ := (h₃ (n - 1)).isZero_homology
  have : Epi (HomologicalComplex.homologyMap S.f n) :=
    (hS.homology_exact₂ n).epi_f_iff.mpr (hz₀.eq_of_tgt _ _)
  have : Mono (HomologicalComplex.homologyMap S.f n) :=
    (hS.homology_exact₁ (n - 1) n (by change (n - 1) + 1 = n; omega)).mono_g_iff.mpr (hz₁.eq_of_src _ _)
  exact isIso_of_mono_of_epi _

end SerrePositivity.KST.DerivedGeometry
