module

public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import SerrePositivity.HomologicalAlgebra.Basic
public import SerrePositivity.PerfectComplex.NormalizedEuler
public import SerrePositivity.PerfectComplex.K0
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# 台つき完全複体の通常の Euler 評価

Noether 環 `T` 上で、台のイデアルの商が Artin 環なら、完全複体のホモロジーは有限長になる。
この有限性を用いて通常の Euler 評価 `chiOrd` を `K₀` 上の準同型にする。
有限性の主張には、長さ代数や正規化基底の選択は必要ない。

ホモトピー不変性と写像錐の加法性は、`NormalizedEuler.lean` の一般定理に通常の長さを
代入して示す。最後に、環自己同型に沿う係数制限、特に群作用によるひねりが評価を保つことを示す。
無限長を零に移す定義上の規約と、有限長を仮定した加法性を区別して扱う。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {T : Type u} [CommRing T] [IsNoetherianRing T]

/-- Noether 環上で、台を指定するイデアルによる商環が Artin 環なら、
その台をもつ有界有限自由複体の各ホモロジーは有限長である。 -/
theorem homology_finiteLength_of_isPerfectSupported {e : ℕ} {w : Fin e → T}
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))]
    {P : CochainComplex (ModuleCat.{u} T) ℤ} (hP : IsPerfectSupported w P) (i : ℤ) :
    IsFiniteLength T (P.homology i) := by
  have := hP.finite i
  have := homology_moduleFinite P i
  exact isFiniteLength_of_le_radical_annihilator _ _ (hP.supported.le_radical_annihilator i)

omit [IsNoetherianRing T] in
/-- 通常の Euler 評価はホモトピー同値で不変である。ホモロジーの長さの有限性は不要である。 -/
lemma chiOrd_eq_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} T) ℤ}
    (h : HomotopyEquiv P Q) : chiOrd P = chiOrd Q := by
  rw [chiOrd_eq_lambdaEuler_ordinary, chiOrd_eq_lambdaEuler_ordinary]
  exact lambdaEuler_eq_of_homotopyEquiv _ h

omit [IsNoetherianRing T] in
/-- 有界性とホモロジーの有限長性のもとで、通常の Euler 評価は写像錐に対して加法的である。
正規化長さの一般定理に `NormalizedLength.ordinary` を適用する。零イデアルの冪ねじれ条件は自動である。 -/
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

/-- Noether 環上で台を指定するイデアルの商が Artin 環であるとき、
通常の Euler 評価を台つき完全複体の `K₀` から実数への加法群準同型として定義する。 -/
noncomputable def chiOrdHom {e : ℕ} (w : Fin e → T)
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))] : K0Supported T w →+ ℝ :=
  K0.lift (fun P ↦ chiOrd P.1)
    (fun _ _ h ↦ chiOrd_eq_of_homotopyEquiv h)
    (fun P Q f hc ↦ chiOrd_cone f Q.2.bounded hc.bounded
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported P.2 i))
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported Q.2 i))
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported hc i)))

/-- 通常の Euler 準同型を複体の類に適用すると、その複体の `chiOrd` に一致する。 -/
@[simp]
lemma chiOrdHom_mk {e : ℕ} (w : Fin e → T)
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))] (P : PerfSupp T w) :
    chiOrdHom w (K0.mk P) = chiOrd P.1 := K0.lift_mk _ _ _ _

/-! ## 環自己同型に沿う係数制限 -/

omit [IsNoetherianRing T] in
/-- 環自己同型に沿う係数制限で、通常の Euler 評価は変わらない。
長さの比較とホモロジーとの両立による。有限長性・有界性の仮定は不要である。 -/
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
/-- 群の元によるひねりは環自己同型に沿う係数制限なので、通常の Euler 評価を保つ。 -/
lemma chiOrd_twist {G : Type u} [Group G] [MulSemiringAction G T]
    (g : G) (P : CochainComplex (ModuleCat.{u} T) ℤ) : chiOrd (twist g P) = chiOrd P :=
  chiOrd_restrictScalars_equiv (MulSemiringAction.toRingEquiv G T g) P

end SerrePositivity
