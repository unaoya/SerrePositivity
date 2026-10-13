module

public import SerrePositivity.LengthAlgebra.KoszulRestriction
public import SerrePositivity.LengthAlgebra.KoszulCokernelBounds
public import SerrePositivity.CommutativeAlgebra.KoszulResolution

/-! # 第零 Koszul ホモロジーの長さの単調性

列の生成イデアルを大きくすると、係数代数の第零 Koszul ホモロジーは商になる。
代数上の商加群との同型と実際の商写像を底環へ係数制限し、正規化長さの単調性を適用する。
列の長さは異なってよく、係数代数の Noether 性や有限生成性は要求しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.LengthAlgebra
open CategoryTheory

variable {S C : Type u} [CommRing S] [CommRing C] [Algebra S C]

/-- 代数を係数とする第零 Koszul ホモロジーを、係数代数の商を底環へ制限した加群と同定する。
環準同型からの作用と通常の代数作用の違いは、既存の Koszul 制限同型で処理する。 -/
def koszulModuleHomologyZeroQuotientIso {r : ℕ} (z : Fin r → S) :
    ((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology 0 ≅
      (ModuleCat.restrictScalars (algebraMap S C)).obj
        (ModuleCat.of C (C ⧸ Ideal.span (Set.range (algebraMap S C ∘ z)))) :=
  koszulModuleAlgebraHomologyIso z 0 ≪≫
    (ModuleCat.restrictScalars (algebraMap S C)).mapIso
      (LinearEquiv.toModuleIso
        (X₁ := (koszulComplex (algebraMap S C ∘ z)).homology 0)
        (X₂ := ModuleCat.of C (C ⧸ Ideal.span (Set.range (algebraMap S C ∘ z))))
        (koszulComplex_homology_zero_equiv (algebraMap S C ∘ z)).some)

/-- 生成イデアルの包含から、代数係数の第零 Koszul ホモロジー間の全射を作る。
商写像を C 線形に作り、S へ制限して両側の Koszul モデルへ戻す。 -/
theorem exists_surjective_koszulModuleHomology_zero_of_span_le
    {r e : ℕ} (w : Fin r → S) (z : Fin e → S)
    (hspan : Ideal.span (Set.range w) ≤ Ideal.span (Set.range z)) :
    ∃ f : ((koszulModuleFunctor w).obj (ModuleCat.of S C)).homology 0 →ₗ[S]
      ((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology 0,
      Function.Surjective f := by
  have hC : Ideal.span (Set.range (algebraMap S C ∘ w)) ≤
      Ideal.span (Set.range (algebraMap S C ∘ z)) := by
    simpa only [Ideal.map_span, ← Set.range_comp] using
      Ideal.map_mono (f := algebraMap S C) hspan
  let qw := C ⧸ Ideal.span (Set.range (algebraMap S C ∘ w))
  let qz := C ⧸ Ideal.span (Set.range (algebraMap S C ∘ z))
  let q : (ModuleCat.restrictScalars (algebraMap S C)).obj (ModuleCat.of C qw) ⟶
      (ModuleCat.restrictScalars (algebraMap S C)).obj (ModuleCat.of C qz) :=
    (ModuleCat.restrictScalars (algebraMap S C)).map
      (ModuleCat.ofHom (Ideal.Quotient.factorₐ C hC).toLinearMap)
  have hq : Function.Surjective q.hom := Ideal.Quotient.factor_surjective hC
  let ew := (koszulModuleHomologyZeroQuotientIso (C := C) w).toLinearEquiv
  let ez := (koszulModuleHomologyZeroQuotientIso (C := C) z).toLinearEquiv
  refine ⟨ez.symm.toLinearMap ∘ₗ q.hom ∘ₗ ew.toLinearMap, ?_⟩
  exact ez.symm.surjective.comp (hq.comp ew.surjective)

/-- 列の生成イデアルが大きくなると、第零 Koszul ホモロジーの正規化長さは減少する。
測定イデアルの有限生成性と元の列への台の条件から、全射の源の冪ねじれ性だけを供給する。 -/
theorem lambdaKoszul_homology_zero_le_of_span_le {J : Ideal S}
    (lam : NormalizedLength S J) (C : Type u) [CommRing C] [Algebra S C]
    (hfg : J.FG) {r e : ℕ}
    (w : Fin r → S) (z : Fin e → S)
    (hJ : J ≤ (Ideal.span (Set.range w)).radical)
    (hspan : Ideal.span (Set.range w) ≤ Ideal.span (Set.range z)) :
    lam.len (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology 0) ≤
      lam.len (((koszulModuleFunctor w).obj (ModuleCat.of S C)).homology 0) := by
  obtain ⟨f, hf⟩ := exists_surjective_koszulModuleHomology_zero_of_span_le (C := C) w z hspan
  exact lam.len_le_of_surjective f hf
    (isPowTorsion_koszulModuleHomology hfg w hJ (ModuleCat.of S C) 0)

/-- 二段の係数制限で測る第零 Koszul ホモロジーの長さは、係数代数の商を
基底環の標準写像で制限した長さと一致する。商の R 作用を環準同型から明示的に構成する。 -/
theorem length_comap_koszulModuleHomology_zero_quotient
    {R S C : Type u} [CommRing R] [CommRing S] [CommRing C]
    [Algebra R S] [Algebra S C] [Algebra R C] [IsScalarTower R S C]
    {J : Ideal R} (lam : NormalizedLength R J) (K : Ideal S)
    (hK : J.map (algebraMap R S) ≤ K) {r : ℕ} (z : Fin r → S) :
    (lam.comap (algebraMap R S) K hK).len
      (((koszulModuleFunctor z).obj (ModuleCat.of S C)).homology 0) =
    (let _ := Module.compHom (C ⧸ Ideal.span (Set.range (algebraMap S C ∘ z)))
      (algebraMap R C)
     lam.len (C ⧸ Ideal.span (Set.range (algebraMap S C ∘ z)))) := by
  rw [length_comap_koszulModuleHomology lam K hK z 0]
  let H := (koszulComplex (algebraMap S C ∘ z)).homology 0
  let Q := C ⧸ Ideal.span (Set.range (algebraMap S C ∘ z))
  let : Module R H := Module.compHom H (algebraMap R C)
  let : Module R Q := Module.compHom Q (algebraMap R C)
  exact lam.len_congr H Q
    (((ModuleCat.restrictScalars (algebraMap R C)).mapIso
      (LinearEquiv.toModuleIso
        (X₁ := H) (X₂ := ModuleCat.of C Q)
        (koszulComplex_homology_zero_equiv (algebraMap S C ∘ z)).some)).toLinearEquiv)

end SerrePositivity.LengthAlgebra
