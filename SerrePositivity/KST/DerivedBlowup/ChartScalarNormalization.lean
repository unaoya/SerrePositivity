module

public import SerrePositivity.KST.DerivedBlowup.ChartScalarDGFunctor
public import SerrePositivity.KST.DerivedBlowup.ChartBasisScalarNaturality

/-!
概要：KST §3.1 の規格化チャートの dg 係数変更。
方針：座標の規格化と環射の可換性に沿って微分を移送する。
規約：座標を写してから規格化した表示を行先とする。
使われ方：チャート基底変換との自然性の可換図式。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable {R S : Type u} [CommRing R] [CommRing S] {I : Type} [DecidableEq I]

omit [DecidableEq I] in
/-- 概要：規格化の係数自然性が誘導するチャート微分の等式。
方針：各座標の自然性を微分の座標引数へ写す。
規約：KST §3.1。使われ方：規格化チャートの行先の同定。 -/
theorem chartScalarNormalizedDifferential_eq (φ : R →+* S) (a x : I → R) (k : I)
    (s : Rˣ) :
    chartKoszulDifferential (φ ∘ a) (φ ∘ normalizeCoordinates x s) k =
      chartKoszulDifferential (φ ∘ a)
        (normalizeCoordinates (φ ∘ x) (Units.map φ.toMonoidHom s)) k := by
  congr 1
  funext j
  exact normalizeCoordinates_scalarMap φ x s j

/-- 概要：規格化チャートを写した係数・規格化座標のチャートへ送る dg 関手。
方針：チャートの係数変更に規格化の自然性による微分移送を合成する。
規約：KST §3.1。使われ方：チャート基底変換の係数自然性。 -/
def chartScalarNormalizedDGFunctor (φ : R →+* S) (a x : I → R) (k : I) (s : Rˣ) :
    DGFunctor R (ExteriorKoszulObject (chartKoszulDifferential a (normalizeCoordinates x s) k))
      (DGRestriction φ (ExteriorKoszulObject (chartKoszulDifferential (φ ∘ a)
        (normalizeCoordinates (φ ∘ x) (Units.map φ.toMonoidHom s)) k))) :=
  EnrichedFunctor.comp (Complex R) (chartScalarDGFunctor φ a (normalizeCoordinates x s) k)
    (restrictDGFunctor φ (exteriorDifferentialTransportDGFunctor
      (chartScalarNormalizedDifferential_eq φ a x k s)))

/-- 概要：規格化チャートの dg 係数変更も総外積の標準係数変更で計算できる。
方針：微分移送の恒等生成元写像とチャート係数変更の包含公式を使う。
規約：KST §3.1。使われ方：基底変換の dg 自然性の証明。 -/
theorem chartScalarNormalizedDGFunctor_inclusion (φ : R →+* S) (a x : I → R)
    (k : I) (s : Rˣ)
    (v w : ExteriorKoszulObject (chartKoszulDifferential a (normalizeCoordinates x s) k))
    (q : ℤ) (z : (exteriorKoszulCochain
      (chartKoszulDifferential a (normalizeCoordinates x s) k)).X q) :
    exteriorCochainInclusion (chartKoszulDifferential (φ ∘ a)
        (normalizeCoordinates (φ ∘ x) (Units.map φ.toMonoidHom s)) k) q
        (((chartScalarNormalizedDGFunctor φ a x k s).map v w).f q z) =
      freeExteriorScalarMap φ
        (exteriorCochainInclusion
          (chartKoszulDifferential a (normalizeCoordinates x s) k) q z) := by
  change exteriorCochainInclusion (chartKoszulDifferential (φ ∘ a)
      (normalizeCoordinates (φ ∘ x) (Units.map φ.toMonoidHom s)) k) q
    ((exteriorKoszulCochainMap LinearMap.id
      (chartKoszulDifferential (φ ∘ a) (φ ∘ normalizeCoordinates x s) k)
      (chartKoszulDifferential (φ ∘ a)
        (normalizeCoordinates (φ ∘ x) (Units.map φ.toMonoidHom s)) k) _).f q
      (((chartScalarDGFunctor φ a (normalizeCoordinates x s) k).map v w).f q z)) = _
  rw [exteriorCochainInclusion_map, ExteriorAlgebra.map_id]
  exact chartScalarDGFunctor_inclusion φ a (normalizeCoordinates x s) k v w q z

end SerrePositivity.KST.DerivedBlowup
