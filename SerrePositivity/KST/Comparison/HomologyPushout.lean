module

public import SerrePositivity.KST.Comparison.HomologyQuasiIso
public import SerrePositivity.KST.Comparison.HomologyColimits
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# 単射な整数ホモロジー同型の pushout

概要：horn 添付で使う、単射な整数ホモロジー同型の pushout 保存を証明する。
方針：鎖写像の余核の acyclic 性と、pushout の余核の同型を使う。
規約：Waldhausen LNM 1126 §1.7・§1.8 のセル添付をアーベル圏の余核で扱う経路。
使われ方：anodyne map の整数ホモロジー保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits HomologicalComplex

/--
概要：単射なアーベル群値鎖写像の余核列は短完全である。
方針：複体のアーベル圏で標準余核列を使う。
規約：単射性を明示する。
使われ方：余核の acyclic 性と擬同型の比較。
-/
theorem integralChainCokernelSequence_shortExact
    {K L : ChainComplex AddCommGrpCat.{u} ℕ} (f : K ⟶ L) [Mono f] :
    (ShortComplex.cokernelSequence f).ShortExact := by
  exact {
    exact := ShortComplex.cokernelSequence_exact f
    mono_f := by change Mono f; infer_instance }

/--
概要：単射な鎖写像は、その余核が acyclic であるとき、かつそのときに限り擬同型である。
方針：短完全列のホモロジー長完全列で、余核群の消滅と誘導射の単射・全射を対応させる。
規約：非負次数の鎖複体。次数零でも左隣の次数一を使う。
使われ方：単射な擬同型の pushout 保存。
-/
theorem integralChain_quasiIso_iff_cokernel_acyclic
    {K L : ChainComplex AddCommGrpCat.{u} ℕ} (f : K ⟶ L) [Mono f] :
    QuasiIso f ↔ (cokernel f).Acyclic := by
  let S := ShortComplex.cokernelSequence f
  have hS : S.ShortExact := integralChainCokernelSequence_shortExact f
  constructor
  · intro hf
    exact hS.acyclic_X₃ hf
  · intro hC
    have hz (n : ℕ) : IsZero ((cokernel f).homology n) :=
      (exactAt_iff_isZero_homology _ n).mp (hC n)
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    have : Epi (homologyMap f n) :=
      (hS.homology_exact₂ n).epi_f ((hz n).eq_zero_of_tgt _)
    have : Mono (homologyMap f n) :=
      (hS.homology_exact₁ (n + 1) n rfl).mono_g ((hz (n + 1)).eq_zero_of_src _)
    exact isIso_of_mono_of_epi _

/--
概要：アーベル群値鎖複体の pushout は単射な擬同型を保存する。
方針：pushout での単射性と余核の実際の同型を使い、余核の acyclic 性を移す。
規約：非負次数の鎖複体。
使われ方：自由整数鎖複体のセル添付。
-/
theorem integralChain_quasiIso_of_pushout
    {K L K' L' : ChainComplex AddCommGrpCat.{u} ℕ}
    {t : K ⟶ L} {l : K ⟶ K'} {r : L ⟶ L'} {b : K' ⟶ L'}
    (sq : IsPushout t l r b) [Mono t] (ht : QuasiIso t) : QuasiIso b := by
  have : Mono b := Abelian.mono_inr_of_isColimit t l sq.isColimit
  have : IsIso (cokernel.map t b l r sq.w) := isIso_cokernel_map_of_isPushout sq
  apply (integralChain_quasiIso_iff_cokernel_acyclic b).mpr
  have hc := (integralChain_quasiIso_iff_cokernel_acyclic t).mp ht
  intro n
  exact (exactAt_iff_of_quasiIsoAt (cokernel.map t b l r sq.w) n).mp (hc n)

/--
概要：単射な整数ホモロジー同型の pushout は整数ホモロジー同型である。
方針：余極限を保存する自由整数鎖複体へ移し、単射な擬同型の pushout 保存を適用する。
規約：元の単体写像の単射性を要求する。
使われ方：horn 添付による整数ホモロジー保存。
-/
theorem integralHomologyIsomorphism_of_pushout {X Y X' Y' : SSet.{u}}
    {t : X ⟶ Y} {l : X ⟶ X'} {r : Y ⟶ Y'} {b : X' ⟶ Y'}
    (sq : IsPushout t l r b) [Mono t] (ht : IntegralHomologyIsomorphism t) :
    IntegralHomologyIsomorphism b := by
  rw [integralHomologyIsomorphism_iff_unnormalized_quasiIso] at ht ⊢
  exact integralChain_quasiIso_of_pushout (sq.map unnormalizedIntegralChains) ht

end SerrePositivity.KST.Comparison
