module

public import SerrePositivity.KST.ProExcision.ScalarConeBiTower
public import SerrePositivity.HomologicalAlgebra.LocalCohomology.KoszulComparison

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

/-!
# Artin–Rees による cone 長完全列の冪核の零化

概要：有限生成加群の冪核を Artin–Rees で消し、反復 cone 比較に適用する。
方針：固定された標的核の元が十分深いイデアル倍に入れば零となることを使う。
規約：Noether 環と有限生成加群。正則性は要求しない。
使われ方：KST Lemma 4.9・4.10 の列長帰納法の各段。
-/

universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- 概要：有限加群の冪核の塔は Artin–Rees により pro-零。
方針：標的核の部分加群への深い像を零化し、冪倍遷移をそこへ入れる。
規約：標的段ごとに零化指数を選ぶ。使われ方：KST Lemma 4.9・4.10 の各 cone 段。 -/
theorem powerKernelTower_isProZero_artinRees (a : R) (M : ModuleCat.{u} R)
    [Module.Finite R M] : IsProZero (powerKernelTower a M) := by
  intro n
  let I : Ideal R := Ideal.span {a}
  let N := powerKernel a M n
  have he : I ^ n ≤ Module.annihilator R N := by
    rw [show I ^ n = Ideal.span {a ^ n} from Ideal.span_singleton_pow a n]
    apply Ideal.span_le.mpr
    rintro _ rfl
    apply Module.mem_annihilator.mpr
    intro x
    apply Subtype.ext
    exact x.property
  obtain ⟨k, hk⟩ := exists_pow_deep_image_killed I N.subtype
    (Submodule.subtype_injective N) (LinearMap.id : N →ₗ[R] N) n he
  refine ⟨n + k, Nat.le_add_right n k, ?_⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply hk
  change a ^ (n + k - n) • x.val ∈ I ^ k • (⊤ : Submodule R M)
  rw [Nat.add_sub_cancel_left]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow
    (Ideal.subset_span (Set.mem_singleton a)) k) Submodule.mem_top

/-- 概要：一変数の通常冪商と cone ホモロジーの比較を Artin–Rees で証明する。
方針：単射な比較の余核を冪核へ入れ、標的核の深さによる零化を使う。
規約：次次数のホモロジーにのみ有限性を要求。
使われ方：KST Lemma 4.10 の反復 cone 証明の各段。 -/
theorem powerScalarConeComparison_isProIso_artinRees
    (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    [Module.Finite R (K.homology (i + 1))] : IsProIso (powerScalarConeComparison a K i) := by
  apply proIso_of_injective_exact_proZero (powerScalarConeComparison a K i)
    (powerScalarConeConnecting a K i)
  · intro n
    exact scalarConeHomologyComparison_injective (a ^ n) K i
  · intro n x
    change (⟨(Cone.δ (smulId (a ^ n) K) i (i + 1) rfl).hom x, _⟩ :
      powerKernel a (K.homology (i + 1)) n) = 0 ↔ _
    rw [Subtype.ext_iff]
    exact scalarConeHomologyComparison_exact (a ^ n) K i x
  · exact powerKernelTower_isProZero_artinRees a (K.homology (i + 1))

/-- 概要：動く有限ホモロジー上の二重 cone 比較の対角は Artin–Rees により pro 同型。
方針：固定段ごとの一変数比較を Artin–Rees で証明し、対角へ移す。
規約：係数段について指数の一様性を要求しない。
使われ方：KST Lemma 4.10 の列長帰納法の各段。 -/
theorem powerScalarConeBiComparison_diagonal_isProIso_artinRees (a : R)
    (X : Tower (CochainComplex (ModuleCat.{u} R) ℤ)) (i : ℤ)
    (hX : ∀ n, Module.Finite R ((X.obj n).homology (i + 1))) :
    IsProIso (powerScalarConeBiComparison a X i).diagonal := by
  apply BiLevelHom.diagonal_isProIso
  intro n k
  let := hX n
  obtain ⟨m, h, g, hg, gh⟩ := powerScalarConeComparison_isProIso_artinRees a (X.obj n) i k
  refine ⟨m, h, g, ?_, ?_⟩
  · change scalarConeHomologyComparison (a ^ m) (X.obj n) i ≫ g =
      ((powerHomologyQuotientBiTower a X i).row n).transition h
    rw [powerHomologyQuotientBiTower_row_transition]
    exact hg
  · change g ≫ scalarConeHomologyComparison (a ^ k) (X.obj n) i =
      (HomologicalComplex.homologyFunctor _ _ i).map
        (((powerScalarConeBiTower a X).row n).transition h)
    rw [powerScalarConeBiTower_row_transition]
    exact gh

end SerrePositivity.KST.ProExcision
