module

public import SerrePositivity.HomologicalAlgebra.FlatBaseChange
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence

/-!
# 平坦な射を後に合成したときの Tor の消滅

## 概要
固定した次数の Tor の消滅は、平坦な係数変更を後に合成しても保たれる。

## 方針
同じ射影分解を使い、係数変更の合成と平坦なホモロジー比較を適用する。

## 規約
次数ごとの主張で、元の環射の平坦性は要求しない。

## 使われ方
BS 著者版 Construction 6.1 の式 (6) に沿う Tor の上界。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- 概要：平坦な係数変更を後に合成すると Tor の消滅を保つ。
方針：射影分解の二段階の底変換を一段階に比較し、平坦性でホモロジーと交換する。
規約：任意の係数加群、BS 著者版 Construction 6.1 の式 (6)。
使われ方：正則元の商の後の二つの平坦射。 -/
theorem torAlg_subsingleton_postcomp_flat (f : R →+* S) (g : S →+* T) (hg : g.Flat)
    (M : ModuleCat.{u} R) (i : ℕ) (h : Subsingleton (TorAlg f i M)) :
    Subsingleton (TorAlg (g.comp f) i M) := by
  let P := extRes (projectiveResolution M)
  have hP := isResolutionOf_extRes (projectiveResolution M)
  let e₁ := torIsoCochain f hP i
  letI : Subsingleton (TorAlg f i M) := h
  letI : Subsingleton ((baseChange f P).homology (-(i : ℤ))) :=
    e₁.symm.toLinearEquiv.injective.subsingleton
  letI := g.toAlgebra
  letI : Module.Flat S T := hg
  let e₂ := flatBaseChangeHomologyEquiv S T (baseChange f P) (-(i : ℤ))
  letI : Subsingleton ((baseChange g (baseChange f P)).homology (-(i : ℤ))) :=
    e₂.injective.subsingleton
  let e₃ := (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
    (baseChangeCompIso f g P)
  have hZ₀ : IsZero ((baseChange g (baseChange f P)).homology (-(i : ℤ))) :=
    ModuleCat.isZero_of_subsingleton _
  have hZ : IsZero ((HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).obj
      (baseChange g (baseChange f P))) := hZ₀
  letI : Subsingleton ((baseChange (g.comp f) P).homology (-(i : ℤ))) :=
    ModuleCat.subsingleton_of_isZero (hZ.of_iso e₃.symm)
  exact (torIsoCochain (g.comp f) hP i).toLinearEquiv.injective.subsingleton

end SerrePositivity
