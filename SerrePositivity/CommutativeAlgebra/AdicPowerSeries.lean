module

public import SerrePositivity.CommutativeAlgebra.AdicFiniteGeneration
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.MvPowerSeries.Evaluation

/-! # 完備環への有限変数の冪級数評価

係数環に離散位相、評価先に指定イデアルのadic位相を入れ、Mathlibの
冪級数評価を適用する。位相の選択を公開APIの引数へ持ち出さず、係数・変数・
イデアル像の計算を供給する。Noether性・局所性・係数写像の単射性は要求しない。
係数体またはWitt係数を与えた正規化と、完備化のNoether性の証明で共有する。
-/

public section

namespace SerrePositivity

variable {R S : Type*} [CommRing R] [CommRing S]
variable (f : R →+* S) (J : Ideal S) [IsAdicComplete J S]
variable {σ : Type*} [Finite σ] (x : σ → S) (hx : ∀ i, x i ∈ J)

/-- 指定イデアル内の有限列への冪級数評価。完備性をMathlibの位相的条件へ移して構成する。 -/
noncomputable def adicPowerSeriesEval : MvPowerSeries σ R →+* S := by
  let : UniformSpace R := ⊥
  let : WithIdeal S := ⟨J⟩
  let : CompleteSpace S := (IsAdic.isPrecomplete_iff (show IsAdic J from rfl)).mp inferInstance
  let : T2Space S := (IsAdic.isHausdorff_iff (show IsAdic J from rfl)).mp inferInstance
  have he : MvPowerSeries.HasEval x := by
    constructor
    · intro i
      exact WithIdeal.isTopologicallyNilpotent_of_mem (hx i)
    · simp
  exact MvPowerSeries.eval₂Hom (φ := f) continuous_of_discreteTopology he

/-- 評価は係数上で元の環写像と一致する。 -/
@[simp] theorem adicPowerSeriesEval_C (r : R) :
    adicPowerSeriesEval f J x hx (MvPowerSeries.C r) = f r := by
  simp [adicPowerSeriesEval, MvPowerSeries.coe_eval₂Hom]

/-- 評価は各形式変数を指定した元へ送る。 -/
@[simp] theorem adicPowerSeriesEval_X (i : σ) :
    adicPowerSeriesEval f J x hx (MvPowerSeries.X i) = x i := by
  simp [adicPowerSeriesEval, MvPowerSeries.coe_eval₂Hom]

/-- 形式変数のイデアルの像は、指定した元のイデアルである。 -/
theorem adicPowerSeriesEval_map_span :
    (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))).map
      (adicPowerSeriesEval f J x hx) = Ideal.span (Set.range x) := by
  rw [Ideal.map_span, ← Set.range_comp]
  simp only [Function.comp_def, adicPowerSeriesEval_X]

/-- 指定係数を加えたイデアルの像を計算する。混標数では係数にpを指定して使う。 -/
theorem adicPowerSeriesEval_map_span_sup (c : R) :
    (Ideal.span {MvPowerSeries.C c} ⊔
      Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R))).map
        (adicPowerSeriesEval f J x hx) =
      Ideal.span {f c} ⊔ Ideal.span (Set.range x) := by
  rw [Ideal.map_sup, adicPowerSeriesEval_map_span, Ideal.map_span]
  simp only [Set.image_singleton, adicPowerSeriesEval_C]

/-- 変数の像が完備イデアルを生成し、係数がその商へ全射なら、冪級数評価は全射。
商での全射を反映するMathlibの一般定理を用い、局所性・Noether性は使わない。 -/
theorem adicPowerSeriesEval_surjective
    (hspan : Ideal.span (Set.range x) = J)
    (hf : Function.Surjective ((Ideal.Quotient.mk J).comp f)) :
    Function.Surjective (adicPowerSeriesEval f J x hx) := by
  let g := adicPowerSeriesEval f J x hx
  let I : Ideal (MvPowerSeries σ R) := Ideal.span (Set.range MvPowerSeries.X)
  have hmap : I.map g = J := (adicPowerSeriesEval_map_span f J x hx).trans hspan
  have : IsHausdorff (I.map g) S := hmap ▸ inferInstance
  apply surjective_of_mk_map_comp_surjective (I := I) g
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨r, hr⟩ := hf (Ideal.Quotient.mk J y)
  refine ⟨MvPowerSeries.C r, ?_⟩
  change Ideal.Quotient.mk (I.map g) (g (MvPowerSeries.C r)) = _
  rw [adicPowerSeriesEval_C, Ideal.Quotient.eq, hmap]
  exact Ideal.Quotient.eq.mp hr

/-- 有限な閉ファイバーと始域の前完備性から、冪級数評価の有限性を得る。
イデアルHを明示するので、等標数の(X)と混標数の(p,X)の双方に使える。
Hの前完備性は実現側で確認する独立した条件である。 -/
theorem adicPowerSeriesEval_finite [Algebra R S]
    (H : Ideal (MvPowerSeries σ R)) [IsPrecomplete H (MvPowerSeries σ R)]
    (hmap : H.map (adicPowerSeriesEval (algebraMap R S) J x hx) = J)
    [Module.Finite R (S ⧸ J)] :
    (adicPowerSeriesEval (algebraMap R S) J x hx).Finite := by
  let g := adicPowerSeriesEval (algebraMap R S) J x hx
  let : Algebra (MvPowerSeries σ R) S := g.toAlgebra
  let : IsScalarTower R (MvPowerSeries σ R) S :=
    IsScalarTower.of_algebraMap_eq (fun r ↦ (adicPowerSeriesEval_C _ J x hx r).symm)
  let : Module.Finite (MvPowerSeries σ R) (S ⧸ J) :=
    Module.Finite.of_restrictScalars_finite R _ _
  exact finite_algebra_of_finite_quotient_map H S J hmap

/-- 変数イデアルの像で割った商が係数環上有限なら、等標数形の評価は有限。
変数イデアルについての冪級数環の完備性をMathlibから供給する。 -/
theorem adicPowerSeriesEval_finite_of_span [Algebra R S]
    (hspan : Ideal.span (Set.range x) = J) [Module.Finite R (S ⧸ J)] :
    (adicPowerSeriesEval (algebraMap R S) J x hx).Finite := by
  apply adicPowerSeriesEval_finite J x hx
    (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)))
  exact (adicPowerSeriesEval_map_span _ J x hx).trans hspan

end SerrePositivity
