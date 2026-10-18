module

public import SerrePositivity.KST.DerivedBlowup.ChartSemilinearTransition
public import SerrePositivity.KST.DerivedBlowup.ChartBasisScalarNaturality
public import SerrePositivity.KST.DerivedBlowup.RestrictionComposition

/-!
概要：KST §3.1 の異なる係数環を通るチャート遷移の合成計算。
方針：自由外積の係数自然性と Koszul 基底変換の cocycle を組み合わせる。
規約：二つ目の座標像は規格化座標で与え、合成の単元は目標環での積とする。
使われ方：全有限重なりの dg 遷移の合成整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory
open DifferentialGraded DifferentialGraded.ScalarExtension

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  {I : Type} [DecidableEq I]

/-- 概要：二段のチャート遷移の総外積写像は直接遷移の写像と一致する。
方針：係数変更を中間の基底変換と交換し、基底変換の cocycle と係数合成則を使う。
規約：KST §3.1、合成単元は t・ψ(s)。
使われ方：半線形チャート dg 関手の合成律の Hom 計算。 -/
theorem chartSemilinearExterior_comp (φ : R →+* S) (ψ : S →+* T)
    (y : I → S) (z : I → T) (i k l : I) (s : Sˣ) (t : Tˣ)
    (hy : ψ ∘ y = normalizeCoordinates z t) (hs : ↑s = y i) (ht : ↑t = z k)
    (w : ExteriorAlgebra R (ChartIndex i →₀ R)) :
    ExteriorAlgebra.map (koszulGeneratorMap l k z t)
      (freeExteriorScalarMap ψ (ExteriorAlgebra.map (koszulGeneratorMap k i y s)
        (freeExteriorScalarMap φ w))) =
    ExteriorAlgebra.map (koszulGeneratorMap l i z (t * Units.map ψ.toMonoidHom s))
      (freeExteriorScalarMap (ψ.comp φ) w) := by
  rw [freeExteriorScalarMap_natural ψ (koszulGeneratorMap k i y s)
    (koszulGeneratorMap k i (ψ ∘ y) (Units.map ψ.toMonoidHom s))
    (koszulGeneratorMap_scalarMap ψ k i y s), freeExteriorScalarMap_comp, hy]
  change (ExteriorAlgebra.map (koszulGeneratorMap l k z t)).comp
    (ExteriorAlgebra.map (koszulGeneratorMap k i (normalizeCoordinates z t)
      (Units.map ψ.toMonoidHom s))) (freeExteriorScalarMap (ψ.comp φ) w) = _
  rw [ExteriorAlgebra.map_comp_map]
  have hu : ↑(Units.map ψ.toMonoidHom s) = normalizeCoordinates z t i := by
    change ψ (↑s) = _
    rw [hs]
    exact congrFun hy i
  rw [koszulGeneratorMap_cocycle l k i z t (Units.map ψ.toMonoidHom s) ht hu]

omit [DecidableEq I] in
/-- 概要：二段の係数関数の像を合成環射でまとめる。
方針：関数等式を各添字で評価する。
規約：KST §3.1。使われ方：半線形チャート遷移の合成の係数条件。 -/
theorem chartSemilinearCoefficients_comp (φ : R →+* S) (ψ : S →+* T)
    (a : I → R) (b : I → S) (c : I → T) (ha : φ ∘ a = b) (hb : ψ ∘ b = c) :
    (ψ.comp φ) ∘ a = c := by
  funext j
  change ψ (φ (a j)) = c j
  exact (congrArg ψ (congrFun ha j)).trans (congrFun hb j)

omit [DecidableEq I] in
/-- 概要：二段の規格化座標の像を合成単元による規格化でまとめる。
方針：規格化の係数自然性と二重規格化の cocycle を使う。
規約：KST §3.1。使われ方：半線形遷移の合成の座標条件。 -/
theorem chartSemilinearCoordinates_comp (φ : R →+* S) (ψ : S →+* T)
    (x : I → R) (y : I → S) (z : I → T) (s : Sˣ) (t : Tˣ)
    (hx : φ ∘ x = normalizeCoordinates y s) (hy : ψ ∘ y = normalizeCoordinates z t) :
    (ψ.comp φ) ∘ x = normalizeCoordinates z (t * Units.map ψ.toMonoidHom s) := by
  calc
    (ψ.comp φ) ∘ x = ψ ∘ normalizeCoordinates y s := by rw [← hx]; rfl
    _ = normalizeCoordinates (ψ ∘ y) (Units.map ψ.toMonoidHom s) := by
      funext j
      exact normalizeCoordinates_scalarMap ψ y s j
    _ = normalizeCoordinates (normalizeCoordinates z t) (Units.map ψ.toMonoidHom s) := by rw [hy]
    _ = _ := normalizeCoordinates_cocycle z t (Units.map ψ.toMonoidHom s)

omit [DecidableEq I] in
/-- 概要：二段の遷移単元の積は直接遷移の pivot 座標となる。
方針：中間単元の像の規格化座標公式に推移単元の cocycle を適用する。
規約：KST §3.1。使われ方：半線形遷移の合成の単元条件。 -/
theorem chartSemilinearUnit_comp (ψ : S →+* T) (y : I → S) (z : I → T) (i : I)
    (s : Sˣ) (t : Tˣ) (hy : ψ ∘ y = normalizeCoordinates z t) (hs : ↑s = y i) :
    ↑(t * Units.map ψ.toMonoidHom s) = z i := by
  apply transitionUnit_cocycle
  change ψ (↑s) = _
  rw [hs]
  exact congrFun hy i

/-- 概要：異なる係数環を通る二段のチャート dg 遷移は直接遷移と一致する。
方針：係数制限の合成比較を挟み、Hom を総外積の合成公式で比較する。
規約：KST §3.1、合成単元は t・ψ(s)、微分移送も各関手に含める。
使われ方：全有限重なりチャートの dg 図式の合成整合性。 -/
theorem chartSemilinearDGFunctor_comp (φ : R →+* S) (ψ : S →+* T)
    (a x : I → R) (b y : I → S) (c z : I → T) (i k l : I) (s : Sˣ) (t : Tˣ)
    (ha : φ ∘ a = b) (hx : φ ∘ x = normalizeCoordinates y s)
    (hk : y k = 1) (hs : ↑s = y i)
    (hb : ψ ∘ b = c) (hy : ψ ∘ y = normalizeCoordinates z t)
    (hl : z l = 1) (ht : ↑t = z k) :
    EnrichedFunctor.comp (Complex R)
      (EnrichedFunctor.comp (Complex R) (chartSemilinearDGFunctor φ a x b y i k s ha hx hk hs)
        (restrictDGFunctor φ (chartSemilinearDGFunctor ψ b y c z k l t hb hy hl ht)))
      (restrictionCompositionDGFunctor φ ψ
        (ExteriorKoszulObject (chartKoszulDifferential c z l))) =
    chartSemilinearDGFunctor (ψ.comp φ) a x c z i l (t * Units.map ψ.toMonoidHom s)
      (chartSemilinearCoefficients_comp φ ψ a b c ha hb)
      (chartSemilinearCoordinates_comp φ ψ x y z s t hx hy) hl
      (chartSemilinearUnit_comp ψ y z i s t hy hs) := by
  refine EnrichedFunctor.ext (Complex R)
    (F := EnrichedFunctor.comp (Complex R)
      (EnrichedFunctor.comp (Complex R) (chartSemilinearDGFunctor φ a x b y i k s ha hx hk hs)
        (restrictDGFunctor φ (chartSemilinearDGFunctor ψ b y c z k l t hb hy hl ht)))
      (restrictionCompositionDGFunctor φ ψ
        (ExteriorKoszulObject (chartKoszulDifferential c z l))))
    (G := chartSemilinearDGFunctor (ψ.comp φ) a x c z i l (t * Units.map ψ.toMonoidHom s)
      (chartSemilinearCoefficients_comp φ ψ a b c ha hb)
      (chartSemilinearCoordinates_comp φ ψ x y z s t hx hy) hl
      (chartSemilinearUnit_comp ψ y z i s t hy hs)) (fun _ => rfl) ?_
  intro v w
  simp only [eqToHom_refl, Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w₀
  apply exteriorCochainInclusion_injective (chartKoszulDifferential c z l) q
  change exteriorCochainInclusion (chartKoszulDifferential c z l) q
    (((chartSemilinearDGFunctor ψ b y c z k l t hb hy hl ht).map _ _).f q
      (((chartSemilinearDGFunctor φ a x b y i k s ha hx hk hs).map v w).f q w₀)) =
    exteriorCochainInclusion (chartKoszulDifferential c z l) q
      (((chartSemilinearDGFunctor (ψ.comp φ) a x c z i l (t * Units.map ψ.toMonoidHom s)
        (chartSemilinearCoefficients_comp φ ψ a b c ha hb)
        (chartSemilinearCoordinates_comp φ ψ x y z s t hx hy) hl
        (chartSemilinearUnit_comp ψ y z i s t hy hs)).map v w).f q w₀)
  rw [chartSemilinearDGFunctor_inclusion, chartSemilinearDGFunctor_inclusion,
    chartSemilinearDGFunctor_inclusion]
  exact chartSemilinearExterior_comp φ ψ y z i k l s t hy hs ht _

end SerrePositivity.KST.DerivedBlowup
