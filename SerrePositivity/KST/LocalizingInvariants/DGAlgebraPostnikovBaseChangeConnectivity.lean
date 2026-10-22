module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovBaseChangedLayer
public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackHomology

/-!
概要：元の隣接 Postnikov 拡大の任意の実底変更は、元と同じ連結度を持つ。
方針：下段射の同値性を仮定せず、元の遷移と kernel の実比較から各次数を判定する。
規約：底変更保存の一般定理を入力しない。使われ方：元の不変量値の連結度。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0] (n : ℤ)
  {P : Mon (Complex R)} (b : P ⟶ postnikov R B n)

lemma postnikovExtensionBaseChangeBase_quasiIsoAt (i : ℤ) (hi : -n ≤ i) :
    QuasiIsoAt (postnikovExtensionBaseChangeBase R B n b).hom i := by
  let q := (postnikovTransition R B (n + 1) n (by omega)).hom
  have hq (j : ℤ) (hj : -n ≤ j) : QuasiIsoAt q j :=
    postnikovTransition_quasiIsoAt R B (n + 1) n (by omega) j hj
  apply cochainPullback_fst_quasiIsoAt b.hom q i
  · by_cases hj : -n ≤ i - 1
    · have := hq (i - 1) hj
      infer_instance
    · exact ((postnikov R B n).X.isZero_of_isGE (-n) (i - 1) (by omega)).epi _
  · have := hq i hi
    infer_instance
  · have := hq (i + 1) (by omega)
    infer_instance

lemma postnikovExtensionBaseChangeBase_homology_epi :
    Epi (homologyMap (postnikovExtensionBaseChangeBase R B n b).hom (-(n + 1))) := by
  let p := (postnikovExtensionBaseChangeBase R B n b).hom
  have he := postnikovBaseChangedKernelIso R B n b
  have : QuasiIso he.hom := quasiIso_of_isIso _
  have hx : (kernel p).ExactAt (-(n + 1) + 1) :=
    (exactAt_iff_of_quasiIsoAt he.hom _).2
      (postnikovKernel_exactAt_above R B n _ (by omega))
  have hz := (exactAt_iff_isZero_homology _ _).1 hx
  have : Epi p := postnikovExtensionBaseChangeBase_epi R B n b
  exact ((cochainKernelSequence_shortExact p).homology_exact₃
    (-(n + 1)) (-(n + 1) + 1) rfl).epi_f (hz.eq_of_tgt _ _)

lemma postnikovExtensionBaseChangeBase_connected :
    IsConnected R (postnikovExtensionBaseChangeBase R B n b) (n + 1) := by
  have hi (j : ℤ) (hj : j ≤ n) :
      Function.Bijective ((groups R j).map (postnikovExtensionBaseChangeBase R B n b)).hom :=
    (groups_map_bijective_iff R _ j).2
      (postnikovExtensionBaseChangeBase_quasiIsoAt R B n b (-j) (by omega))
  constructor
  · intro j hj
    exact (hi j (by omega)).1
  · intro j hj
    by_cases h : j ≤ n
    · exact (hi j h).2
    · have hj' : j = n + 1 := by omega
      subst j
      exact (ModuleCat.epi_iff_surjective _).1
        (postnikovExtensionBaseChangeBase_homology_epi R B n b)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
