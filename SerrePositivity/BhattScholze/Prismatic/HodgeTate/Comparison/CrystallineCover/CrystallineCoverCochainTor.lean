module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoverFactorization
public import SerrePositivity.HomologicalAlgebra.RegularQuotientUnboundedModel

/-!
# 結晶被覆の非有界な mod p の Tor 振幅

## 概要
任意の複体の半自由分解上の底変換を使い、式 (6) の Tor 振幅一を評価する。

## 方針
正則主元の商を実際の Koszul 模型で計算し、後の二つの平坦射で下界を保つ。

## 規約
BS 著者版 Construction 6.1、Construction 6.1。上に有界という制限を置かない。

## 使われ方
完全 Tor 振幅三の評価と Prop 6.2 の保存性。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity.BhattScholze.Prismatic.Construction61
open CategoryTheory CategoryTheory.Limits DifferentialGraded

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- 概要：被覆の mod p の底変換は非有界な複体の下界を高々一だけ下げる。
方針：実際の K-flat 分解と Koszul 増大の比較を式 (6) の平坦な後半に接続する。
規約：BS 著者版 Construction 6.1、Construction 6.1 の二つの入力を明示する。
使われ方：数値の Tor 消滅から任意の入力の鎖複体の評価へ進む。 -/
theorem modPBaseChange_homology_isZero_below
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    {L K : CochainComplex (ModuleCat.{u} (ModP A p)) ℤ} (q : L ⟶ K) [QuasiIso q]
    (hL : complexKFlat (ModP A p) L) (m : ℤ)
    (hK : ∀ i : ℤ, i < m → IsZero (K.homology i))
    (i : ℤ) (hi : i < m - 1) :
    IsZero ((baseChange (alphaModP P) L).homology i) := by
  let x : Fin 1 → ModP A p := fun _ => coverModPGenerator P
  have hx : IsKoszulResolution x := by
    apply isKoszulResolution_of_isWeaklyRegular
    rw [show List.ofFn x = [coverModPGenerator P] by simp [x, List.ofFn_succ]]
    exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr
      (generator_modP_regular P hR)
  have he : Set.range x = {coverModPGenerator P} := by ext a; simp [x]
  let q₀ := Ideal.Quotient.mk (Ideal.span {coverModPGenerator P})
  have h₀ : ∀ j : ℤ, j < m - 1 → IsZero ((baseChange q₀ L).homology j) := by
    intro j hj
    have hz := regularQuotientBaseChange_homology_isZero_below x hx q hL m hK j hj
    let G (s : Set (ModP A p)) : Prop :=
      IsZero ((baseChange (Ideal.Quotient.mk (Ideal.span s)) L).homology j)
    exact Eq.mp (congrArg G he) (show G (Set.range x) from hz)
  let g := (coverResidueFlatMap P hR).comp (residueFrobenius P)
  have hg : g.Flat := (residueFrobenius_faithfullyFlat P hF).flat.comp
    (coverResidueFlatMap_faithfullyFlat P hR).flat
  have h₁ := flatBaseChange_homology_isZero_below g hg (baseChange q₀ L) (m - 1) h₀ i hi
  let e := (HomologicalComplex.homologyFunctor _ _ i).mapIso (baseChangeCompIso q₀ g L)
  have h₂ : IsZero ((baseChange (g.comp q₀) L).homology i) := h₁.of_iso e.symm
  have hf : alphaModP P = g.comp q₀ := alphaModP_factorization P hR
  simpa only [← hf] using h₂

/-- 概要：任意の非有界複体について、振幅一を満たす実際の導来底変換模型が存在する。
方針：既存の半自由分解を取り、上の下界の評価を全次数に適用する。
規約：BS 著者版 Construction 6.1、Construction 6.1。模型の存在を仮定にしない。
使われ方：一般の導来入力への適用。 -/
theorem exists_modPBaseChange_model
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    (K : CochainComplex (ModuleCat.{u} (ModP A p)) ℤ) (m : ℤ)
    (hK : ∀ i : ℤ, i < m → IsZero (K.homology i)) :
    ∃ (L : CochainComplex (ModuleCat.{u} (ModP A p)) ℤ) (q : L ⟶ K), QuasiIso q ∧
      complexKFlat (ModP A p) L ∧
        ∀ i : ℤ, i < m - 1 → IsZero ((baseChange (alphaModP P) L).homology i) := by
  obtain ⟨L, q, _, hq, _, hL, _⟩ := exists_unbounded_baseChange_model (alphaModP P) K
  letI := hq
  exact ⟨L, q, hq, hL, modPBaseChange_homology_isZero_below P hF hR q hL m hK⟩

/-- 概要：普遍 prism の非有界な mod p の底変換も振幅一。
方針：普遍向き付き prism の d 完全平坦性と A/d の p 正則性を直接入力する。
規約：BS 著者版 Example 3.4、Construction 6.1、Construction 6.1。
使われ方：普遍的な結晶被覆への適用。 -/
theorem universal_exists_modPBaseChange_model
    (K : CochainComplex (ModuleCat.{u} (ModP (UniversalOrientedPrismRing.{u} p) p)) ℤ)
    (m : ℤ) (hK : ∀ i : ℤ, i < m → IsZero (K.homology i)) :
    ∃ (L : CochainComplex (ModuleCat.{u} (ModP (UniversalOrientedPrismRing.{u} p) p)) ℤ)
      (q : L ⟶ K), QuasiIso q ∧ complexKFlat _ L ∧
        ∀ i : ℤ, i < m - 1 →
          IsZero ((baseChange (alphaModP (universalOrientedPrism.{u} p)) L).homology i) :=
  exists_modPBaseChange_model (universalOrientedPrism.{u} p)
    (universalOrientedPrism_frobenius_isCompletelyFlat p)
    (universalOrientedPrism_mod_generator_p_regular p) K m hK

end SerrePositivity.BhattScholze.Prismatic.Construction61
