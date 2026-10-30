module

public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.HomologicalAlgebra.Basic
public import SerrePositivity.PerfectComplex.NormalizedEuler
public import SerrePositivity.PerfectComplex.K0
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# 台つき完全複体の通常の Euler 評価

## 概要

通常の長さ `Module.length` で複体のホモロジーを測った Euler 評価 `chiOrd P = Σ (-1)^i ℓ(H^i(P))`
（`Basic.lean`）を、台つき完全複体の `K₀` 上の準同型 `chiOrdHom : K₀ → ℝ` にする。論文 Lemma 3.5b の
通常の長さ側（`χ_T` が `K_0^{m}(T)` 上の加法的関数であること）に当たる。

## 内容

- 有限性：Noether 環 `T` 上、台のイデアル `(w)` による商 `T/(w)` が Artin 環なら、`w` に台をもつ
  完全複体のホモロジーは有限長（`homology_finiteLength_of_isPerfectSupported`）。台の条件から
  ホモロジーは `(w)` の冪で消える（`Support.lean`）ので、`CommutativeAlgebra/FiniteLength.lean` の
  判定が使える。論文の設定では `T/(z)T = T/m_A T` が `A/m_A` 上有限次元なので Artin 環である。
- ホモトピー不変性と写像錐の加法性（`chiOrd_eq_of_homotopyEquiv`、`chiOrd_cone`）：
  `NormalizedEuler.lean` の一般定理に `NormalizedLength.ordinary` を代入する。`J = ⊥` の冪ねじれ条件は
  自動的にみたされる（`IsPowTorsion.bot`）。
- `chiOrdHom`：以上を `K0.lift` でまとめる。
- ひねりでの不変性（`chiOrd_twist`）：環自己同型に沿った係数制限は長さを変えない
  （`FiniteLength.lean` の `length_restrictScalars_equiv`）。§5 で `χ(g^*P) = χ(P)` に使う。

## 規約

`chiOrd` は無限長を `0` と数える（`toNat`）。加法性 `chiOrd_cone` は有限長を仮定した主張であり、
規約による値については何も言わない。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {T : Type u} [CommRing T] [IsNoetherianRing T]

/-- Noether 環 `T` 上、`T/(w)` が Artin 環なら、`w` に台をもつ完全複体 `P` の各ホモロジー `H^i(P)` は
有限長である。`H^i(P)` は有限生成（項が有限生成で `T` が Noether）で、台の条件から
`(w) ⊆ √(Ann H^i(P))`（`IsSupported.le_radical_annihilator`）なので、
`isFiniteLength_of_le_radical_annihilator` が使える。長さ代数や正規化基底の選択は要らない。 -/
theorem homology_finiteLength_of_isPerfectSupported {e : ℕ} {w : Fin e → T}
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))]
    {P : CochainComplex (ModuleCat.{u} T) ℤ} (hP : IsPerfectSupported w P) (i : ℤ) :
    IsFiniteLength T (P.homology i) := by
  have := hP.finite i
  have := homology_moduleFinite P i
  exact isFiniteLength_of_le_radical_annihilator _ _ (hP.supported.le_radical_annihilator i)

omit [IsNoetherianRing T] in
/-- `chiOrd` はホモトピー同値で不変（`lambdaEuler_eq_of_homotopyEquiv` の特殊化）。有限性は要らない。 -/
lemma chiOrd_eq_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} T) ℤ}
    (h : HomotopyEquiv P Q) : chiOrd P = chiOrd Q := by
  rw [chiOrd_eq_lambdaEuler_ordinary, chiOrd_eq_lambdaEuler_ordinary]
  exact lambdaEuler_eq_of_homotopyEquiv _ h

omit [IsNoetherianRing T] in
/-- **写像錐についての加法性**：`Q` と `Cone f` が有界で、`P`、`Q`、`Cone f` のホモロジーが有限長なら
`χ(Cone f) = χ(Q) - χ(P)`。`lambdaEuler_cone` に `NormalizedLength.ordinary` を代入する。`J = ⊥` の
冪ねじれ条件は `IsPowTorsion.bot` で自動、`ℕ∞` の有限性を `ℝ≥0∞` の有限性に移す。 -/
theorem chiOrd_cone {P Q : CochainComplex (ModuleCat.{u} T) ℤ} (f : P ⟶ Q)
    (hQ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (Q.X i))
    (hC : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone f).X i))
    (lP : ∀ i, Module.length T (P.homology i) ≠ ⊤)
    (lQ : ∀ i, Module.length T (Q.homology i) ≠ ⊤)
    (lC : ∀ i, Module.length T ((Cone.cone f).homology i) ≠ ⊤) :
    chiOrd (Cone.cone f) = chiOrd Q - chiOrd P := by
  simp only [chiOrd_eq_lambdaEuler_ordinary]
  exact lambdaEuler_cone _ f hQ hC (fun _ ↦ IsPowTorsion.bot) (fun _ ↦ IsPowTorsion.bot)
    (fun _ ↦ IsPowTorsion.bot) (fun i ↦ ENat.toENNReal_ne_top.mpr (lP i))
    (fun i ↦ ENat.toENNReal_ne_top.mpr (lQ i)) (fun i ↦ ENat.toENNReal_ne_top.mpr (lC i))

/-- Noether 環 `T` 上、`T/(w)` が Artin 環のとき、`chiOrd` を `K₀^{(w)}(T)` から `ℝ` への準同型に
降ろしたもの。`K0.lift` にホモトピー不変性と錐の関係式（有限性は
`homology_finiteLength_of_isPerfectSupported` で供給）を渡す。Lemma 3.5b の通常の長さ側
（`Paper/Lemma3_5/Ordinary.lean`）で `K0.hom_ext_koszul` と組み合わせて使う。 -/
noncomputable def chiOrdHom {e : ℕ} (w : Fin e → T)
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))] : K0Supported T w →+ ℝ :=
  K0.lift (fun P ↦ chiOrd P.1)
    (fun _ _ h ↦ chiOrd_eq_of_homotopyEquiv h)
    (fun P Q f hc ↦ chiOrd_cone f Q.2.bounded hc.bounded
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported P.2 i))
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported Q.2 i))
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported hc i)))

/-- `chiOrdHom w [P] = chiOrd P`。 -/
@[simp]
lemma chiOrdHom_mk {e : ℕ} (w : Fin e → T)
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))] (P : PerfSupp T w) :
    chiOrdHom w (K0.mk P) = chiOrd P.1 := K0.lift_mk _ _ _ _

/-! ## 環自己同型に沿う係数制限 -/

omit [IsNoetherianRing T] in
/-- 環自己同型 `σ : T ≃+* T` に沿って複体の係数を制限しても `chiOrd` は変わらない。係数制限は圏同値
なのでホモロジーと可換で（`mapHomologyIso`）、環自己同型に沿った係数制限は加群の長さを変えない
（`length_restrictScalars_equiv`）から。有限長性・有界性の仮定は要らない。 -/
lemma chiOrd_restrictScalars_equiv (σ : T ≃+* T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    chiOrd (((ModuleCat.restrictScalars σ.toRingHom).mapHomologicalComplex _).obj P) =
      chiOrd P := by
  let F := ModuleCat.restrictScalars.{u} σ.toRingHom
  have : F.IsEquivalence := inferInstance
  unfold chiOrd
  congr 1
  funext i
  let e : ((F.mapHomologicalComplex _).obj P).homology i ≅ F.obj (P.homology i) :=
    (P.sc i).mapHomologyIso F
  rw [e.toLinearEquiv.length_eq, length_restrictScalars_equiv]

omit [IsNoetherianRing T] in
/-- ひねりは `chiOrd` を保つ：`χ(g^*P) = χ(P)`。ひねりは環自己同型 `g •` に沿った係数制限だから。
§5（`Paper/Section5/`）で、`G` 軌道の和の `χ` を計算するときに使う。 -/
lemma chiOrd_twist {G : Type u} [Group G] [MulSemiringAction G T]
    (g : G) (P : CochainComplex (ModuleCat.{u} T) ℤ) : chiOrd (twist g P) = chiOrd P :=
  chiOrd_restrictScalars_equiv (MulSemiringAction.toRingEquiv G T g) P

end SerrePositivity
