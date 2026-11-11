module

public import SerrePositivity.HomologicalAlgebra.RegularQuotientUnboundedModel

/-!
# 非有界な K-flat 模型の正則なスカラーの錐

## 概要
正則元のスカラー錐を、その通常商への実際の底変換に比較して消滅を移す。

## 方針
一元 Koszul の標準増大と、全テンソルの反復錐表示を使う。

## 規約
BS 著者版 Construction 6.1 の標的の p に適用する。複体の上の有界性は不要。

## 使われ方
完全 Koszul の下界を mod p の底変換から得る。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits DifferentialGraded DerivedCompletion

variable {R : Type u} [CommRing R]

/-- 概要：正則なスカラーの通常商への底変換の消滅を、K-flat 模型のスカラー錐へ移す。
方針：一元 Koszul と通常商の標準増大をテンソルし、ホモロジーの同型で移す。
規約：任意の非有界複体、BS 著者版 Construction 6.1 の完全振幅の計算。
使われ方：結晶被覆上の p の因子の評価。 -/
theorem scalarCone_homology_isZero_of_regular_quotient
    (a : R) (ha : IsSMulRegular R a) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : complexKFlat R K) (i : ℤ)
    (hQ : IsZero ((baseChange (Ideal.Quotient.mk (Ideal.span {a})) K).homology i)) :
    IsZero (((scalarConeFunctor a).obj K).homology i) := by
  let x : Fin 1 → R := fun _ => a
  have hx : IsKoszulResolution x := by
    apply isKoszulResolution_of_isWeaklyRegular
    rw [show List.ofFn x = [a] by simp [x, List.ofFn_succ]]
    exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr ha
  have he : Set.range x = {a} := by ext b; simp [x]
  let Q := R ⧸ Ideal.span (Set.range x)
  let q := Ideal.Quotient.mk (Ideal.span (Set.range x))
  let G (s : Set R) : Prop :=
    IsZero ((baseChange (Ideal.Quotient.mk (Ideal.span s)) K).homology i)
  have h₀ : IsZero ((baseChange q K).homology i) :=
    Eq.mpr (congrArg G he) (show G {a} from hQ)
  have hs := ModuleCat.subsingleton_of_isZero h₀
  have hsR : Subsingleton ((ModuleCat.restrictScalars q).obj ((baseChange q K).homology i)) := hs
  letI := hsR
  have h₁ : IsZero ((ModuleCat.restrictScalars q).obj ((baseChange q K).homology i)) :=
    ModuleCat.isZero_of_subsingleton _
  have h₂ := h₁.of_iso ((restrictCochainHomologyIso (R := R) (C := Q) i).app (baseChange q K))
  letI := regularQuotientTensorComparison_quasiIso x hx K hK
  have h₃ := h₂.of_iso (asIso
    (HomologicalComplex.homologyMap (regularQuotientTensorComparison x hx K) i))
  let F := HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) i
  have h₄ := h₃.of_iso (F.mapIso (koszulCochainTensorIso x K)).symm
  exact h₄

end SerrePositivity
