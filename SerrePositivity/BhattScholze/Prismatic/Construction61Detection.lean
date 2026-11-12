module

public import SerrePositivity.BhattScholze.Prism.Basic.CrystallineCoverPairTor
public import SerrePositivity.HomologicalAlgebra.CompleteBaseChangeConservative

/-!
# Construction 6.1 の非有界な完備底変換の検出

## 概要
結晶被覆への二座標完備底変換が非輪状なら、元の (p,d) 完備な複体も非輪状である。

## 方針
式 (6) の忠実平坦な剰余と正則列 (p,d) を一般の Koszul Nakayama へ入れる。

## 規約
BS 著者版 Proposition 6.2、D77。通常の Frobenius 平坦性を普遍例に仮定しない。

## 使われ方
Theorem 6.3 の帰着の古典的な入力。HT 比較と Tot の組み立ては含めない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.BhattScholze.Prismatic.Construction61
open CategoryTheory CategoryTheory.Limits DifferentialGraded DerivedCompletion InfinityCategories
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- 概要：結晶被覆への二座標完備底変換の鎖複体の模型。
方針：実際の係数拡大を、標的の二座標 (p,p) で順に主元完備化する。
規約：BS 著者版 Proposition 6.2。K-flat 分解上で導来テンソルを計算する模型である。
使われ方：非有界な入力の零性と擬同型を検出する。 -/
def completedCoverModelFunctor :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤
      CochainComplex (ModuleCat.{u} (crystallineCoverRing P)) ℤ :=
  (ModuleCat.extendScalars (crystallineCoverMap P).toRingHom).mapHomologicalComplex (.up ℤ) ⋙
    complexCompletionFunctor (crystallineCoverRing P) (p : crystallineCoverRing P) ⋙
    complexCompletionFunctor (crystallineCoverRing P) (p : crystallineCoverRing P)

/-- 概要：実際の K-flat 模型の完備底変換が非輪状なら、元の完備複体も非輪状。
方針：式 (6) の (p,d) の商からの忠実平坦性と標的の p 正則性を接続する。
規約：BS 著者版 Proposition 6.2、D77、非有界な複体。
使われ方：半自由分解による一般の導来入力の検出。 -/
theorem cochain_acyclic_of_completedCover_acyclic
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    (L : CochainComplex (ModuleCat.{u} A) ℤ) (hL : complexKFlat A L)
    (hB : complexKFlat (crystallineCoverRing P) (baseChange (crystallineCoverMap P).toRingHom L))
    (hp : IsComplete A (p : A) (DerivedCategory.Q.obj L))
    (hd : IsComplete A P.generator (DerivedCategory.Q.obj L))
    (h : ∀ i : ℤ, IsZero (((completedCoverModelFunctor P).obj L).homology i)) :
    ∀ i : ℤ, IsZero (L.homology i) := by
  apply cochain_acyclic_of_repeatedCompletedBaseChange_acyclic
    (crystallineCoverMap P).toRingHom (p : crystallineCoverRing P)
    (by
      change Function.Injective (fun x : crystallineCoverRing P => (p : crystallineCoverRing P) * x)
      exact crystallineCover_p_regular P) (coverPairCoordinates P)
    (coverPairCoordinates_regular P hR) (coverPairFlatMap P hR)
    (coverPairFlatMap_faithfullyFlat P hF hR) ?_ L hL hB ?_ h
  · have hβ : (Ideal.Quotient.mk (Ideal.span {(p : crystallineCoverRing P)})).comp
        (crystallineCoverMap P).toRingHom = coverMapToModP P := by
      apply RingHom.ext
      intro a
      rfl
    exact hβ.trans (coverMapToModP_factorization P hR)
  · intro j
    fin_cases j
    · exact hp
    · exact hd

/-- 概要：任意の複体の半自由分解で計算した完備底変換の零性を反映する。
方針：分解の擬同型で完備性を移し、模型で検出して元のホモロジーへ戻す。
規約：BS 著者版 Proposition 6.2。入力の有界性を一切課さない。
使われ方：Theorem 6.3 の帰着の鎖複体版。 -/
theorem cochain_acyclic_of_completedCover_resolution_acyclic
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    {L K : CochainComplex (ModuleCat.{u} A) ℤ} (q : L ⟶ K) [QuasiIso q]
    (hL : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A L)
    (hp : IsComplete A (p : A) (DerivedCategory.Q.obj K))
    (hd : IsComplete A P.generator (DerivedCategory.Q.obj K))
    (h : ∀ i : ℤ, IsZero (((completedCoverModelFunctor P).obj L).homology i)) :
    ∀ i : ℤ, IsZero (K.homology i) := by
  let e := asIso (DerivedCategory.Q.map q)
  have hz := cochain_acyclic_of_completedCover_acyclic P hF hR L
    (semifreeComplex_isKFlat hL) (semifreeComplex_baseChange_isKFlat (crystallineCoverMap P).toRingHom hL)
    (isComplete_of_iso A (p : A) e.symm hp)
    (isComplete_of_iso A P.generator e.symm hd) h
  intro i
  exact (hz i).of_iso (asIso (HomologicalComplex.homologyMap q i)).symm

/-- 概要：任意の非有界複体には、完備底変換での検出を備えた実際の半自由模型が存在する。
方針：半自由分解の存在と、上の零性の反映を組み合わせる。
規約：BS 著者版 Proposition 6.2。模型が存在するという仮定に置き換えない。
使われ方：導来テンソルの実際の計算模型の供給。 -/
theorem exists_completedCover_detection_model
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hp : IsComplete A (p : A) (DerivedCategory.Q.obj K))
    (hd : IsComplete A P.generator (DerivedCategory.Q.obj K)) :
    ∃ (L : CochainComplex (ModuleCat.{u} A) ℤ) (q : L ⟶ K), QuasiIso q ∧
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree A L ∧ complexKFlat A L ∧
      complexKFlat (crystallineCoverRing P) (baseChange (crystallineCoverMap P).toRingHom L) ∧
      ((∀ i : ℤ, IsZero (((completedCoverModelFunctor P).obj L).homology i)) →
        ∀ i : ℤ, IsZero (K.homology i)) := by
  obtain ⟨L, q, hsemi, hq, _, hL, hB⟩ :=
    exists_unbounded_baseChange_model (crystallineCoverMap P).toRingHom K
  letI := hq
  exact ⟨L, q, hq, hsemi, hL, hB,
    cochain_acyclic_of_completedCover_resolution_acyclic P hF hR q hsemi hp hd⟩

/-- 概要：普遍 prism の結晶被覆も非有界な完備入力の零性を反映する。
方針：K2 の d 完全平坦性と A/d の p 正則性を直接入力する。
規約：BS 著者版 Proposition 6.2、Example 3.4、D77。
使われ方：Theorem 6.3 の普遍基底への帰着の古典的な入力。 -/
theorem universal_cochain_acyclic_of_completedCover_resolution_acyclic
    {L K : CochainComplex (ModuleCat.{u} (UniversalOrientedPrismRing.{u} p)) ℤ}
    (q : L ⟶ K) [QuasiIso q] (hL : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree _ L)
    (hp : IsComplete _ (p : UniversalOrientedPrismRing.{u} p) (DerivedCategory.Q.obj K))
    (hd : IsComplete _ (universalOrientedPrism.{u} p).generator (DerivedCategory.Q.obj K))
    (h : ∀ i : ℤ, IsZero
      (((completedCoverModelFunctor (universalOrientedPrism.{u} p)).obj L).homology i)) :
    ∀ i : ℤ, IsZero (K.homology i) :=
  cochain_acyclic_of_completedCover_resolution_acyclic (universalOrientedPrism.{u} p)
    (universalOrientedPrism_frobenius_isCompletelyFlat p)
    (universalOrientedPrism_mod_generator_p_regular p) q hL hp hd h

end SerrePositivity.BhattScholze.Prismatic.Construction61
