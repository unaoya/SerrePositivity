module

public import SerrePositivity.HomologicalAlgebra.RegularQuotientUnboundedModel
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# 非有界な複体の忠実平坦な検出

## 概要
忠実平坦な係数拡大は、任意の複体の各次数のホモロジーの消滅を反映する。

## 方針
平坦なホモロジー比較と、忠実平坦なテンソルの零加群の反映を接続する。

## 規約
BS 著者版 Proposition 6.2 の入力。上にも下にも有界性を課さない。

## 使われ方
Construction 6.1 の式 (6) の忠実平坦な後半から Koszul 剰余へ戻る。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits DifferentialGraded
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 概要：忠実平坦な底変換は、非有界な複体の各ホモロジーの消滅を反映する。
方針：平坦なホモロジー比較を通じてテンソルの忠実性を使う。
規約：BS 著者版 Proposition 6.2。使われ方：式 (6) の逆向きの検出。 -/
theorem cochain_homology_isZero_of_faithfullyFlat_baseChange
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (h : IsZero ((baseChange f K).homology i)) : IsZero (K.homology i) := by
  letI := f.toAlgebra
  letI : Module.FaithfullyFlat R S := hf
  let e := flatBaseChangeHomologyEquiv R S K i
  letI := ModuleCat.subsingleton_of_isZero h
  have ht : Subsingleton (TensorProduct R S (K.homology i)) := e.symm.injective.subsingleton
  letI := (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R S).mp ht
  exact ModuleCat.isZero_of_subsingleton _

/-- 概要：正則列の通常商の実際の導来テンソルの消滅は Koszul 模型と同値。
方針：K-flat な複体に対する標準比較射のホモロジー同型を両向きに使う。
規約：BS 著者版 Proposition 6.2、任意の非有界複体。
使われ方：零性を忠実平坦な剰余と完備 Nakayama の間で移す。 -/
theorem regularQuotientBaseChange_homology_isZero_iff
    {r : ℕ} (x : Fin r → R) (hx : IsKoszulResolution x)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (hK : complexKFlat R K) (i : ℤ) :
    IsZero ((baseChange (Ideal.Quotient.mk (Ideal.span (Set.range x))) K).homology i) ↔
      IsZero ((koszulComplexOn x K).homology i) := by
  let Q := R ⧸ Ideal.span (Set.range x)
  let q := Ideal.Quotient.mk (Ideal.span (Set.range x))
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i
  letI := regularQuotientTensorComparison_quasiIso x hx K hK
  let e := (F.mapIso (koszulCochainTensorIso x K)).symm ≪≫
    asIso (HomologicalComplex.homologyMap (regularQuotientTensorComparison x hx K) i) ≪≫
      (restrictCochainHomologyIso (R := R) (C := Q) i).app (baseChange q K)
  constructor
  · intro h
    have hs := ModuleCat.subsingleton_of_isZero h
    letI : Subsingleton ((ModuleCat.restrictScalars q).obj ((baseChange q K).homology i)) := hs
    have hz : IsZero ((ModuleCat.restrictScalars q).obj ((baseChange q K).homology i)) :=
      ModuleCat.isZero_of_subsingleton _
    exact hz.of_iso e
  · intro h
    have hz := h.of_iso e.symm
    have hs := ModuleCat.subsingleton_of_isZero hz
    letI : Subsingleton ((baseChange q K).homology i) := hs
    exact ModuleCat.isZero_of_subsingleton _

end SerrePositivity
