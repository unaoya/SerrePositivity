module

public import SerrePositivity.KST.DerivedBlowup.UniversalPresentation
public import SerrePositivity.KST.DerivedBlowup.ChartComplexes
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
概要：KST Def3.1・Lemma3.6 の普遍係数の任意環への特殊化。
方針：T_j↦a_j を係数評価とし、多項式の底変更同型で普遍チャート関係式を比較する。
規約：基底環と添字型の宇宙は独立。通常の多項式環の tensor 比較を先に固定する。
使われ方：普遍 Koszul 解消から任意係数の導来チャートを得る。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open scoped TensorProduct

variable {R : Type u} [CommRing R] {I : Type v} [DecidableEq I]

/-- 概要：普遍基底の各変数を指定係数へ送る環射。
方針：整数係数を標準射で送り、多項式を a_j で評価する。
規約：KST Def3.1。使われ方：普遍 blowup の基底変更。 -/
def universalSpecialization (a : I → R) : UniversalBase I →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) a

omit [DecidableEq I] in
/-- 概要：普遍基底の生成元の特殊化は指定係数。
方針：eval₂ の生成元公式。
規約：KST Def3.1。使われ方：普遍関係式の特殊化。 -/
@[simp] theorem universalSpecialization_X (a : I → R) (j : I) :
    universalSpecialization a (MvPolynomial.X j) = a j :=
  MvPolynomial.eval₂Hom_X' _ _ _

/-- 概要：チャート多項式環の係数特殊化。
方針：比変数を保ち、係数だけ普遍特殊化で送る。
規約：KST Def3.1。使われ方：普遍 Koszul 生成元微分の底変更。 -/
def universalChartSpecializationMap (a : I → R) (i : I) :
    ChartRing (UniversalBase I) i →+* ChartRing R i :=
  MvPolynomial.map (universalSpecialization a)

/-- 概要：チャート特殊化は普遍関係式を所望のチャート関係式へ送る。
方針：係数・変数・積・差の保存を使う。
規約：KST Lemma3.6。使われ方：導来チャートの Koszul 表示。 -/
@[simp] theorem universalChartSpecializationMap_relation (a : I → R) (i : I)
    (j : ChartIndex i) :
    universalChartSpecializationMap a i (universalRelation i j) = chartRelation R a i j.val := by
  simp [universalChartSpecializationMap, universalRelation, chartRelation, chartCoordinate,
    j.property]

/-- 概要：普遍チャート多項式環の通常の tensor 底変更は係数特殊化後の多項式環。
方針：Mathlib の多変数多項式の代数 tensor 同型を使う。
規約：KST Def3.1、関係式商を取る前の表示環の比較。
使われ方：普遍基底上の Koszul 解消の底変更を計算する。 -/
def universalPresentationBaseChangeEquiv (a : I → R) (i : I) :
    letI := (universalSpecialization a).toAlgebra
    R ⊗[UniversalBase I] ChartRing (UniversalBase I) i ≃ₐ[R] ChartRing R i := by
  letI := (universalSpecialization a).toAlgebra
  exact MvPolynomial.algebraTensorAlgEquiv _ _

/-- 概要：通常の tensor 底変更同型は普遍関係式の純粋 tensor を対応する関係式へ送る。
方針：多項式底変更同型の純粋 tensor 公式と係数特殊化の関係式公式を合わせる。
規約：KST Lemma3.6。使われ方：普遍解消の底変更後の微分の同定。 -/
theorem universalPresentationBaseChangeEquiv_relation (a : I → R) (i : I)
    (j : ChartIndex i) :
    letI := (universalSpecialization a).toAlgebra
    universalPresentationBaseChangeEquiv a i ((1 : R) ⊗ₜ[UniversalBase I] universalRelation i j) =
      chartRelation R a i j.val := by
  let := (universalSpecialization a).toAlgebra
  change MvPolynomial.algebraTensorAlgEquiv _ _ _ = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  exact universalChartSpecializationMap_relation a i j

/-- 概要：普遍チャート特殊化は普遍基底上の代数射である。
方針：係数特殊化を代数準同型として多項式環へ持ち上げる。
規約：KST Def3.1。使われ方：既存のチャート dg 底変更 API への入力。 -/
def universalChartSpecializationAlgHom (a : I → R) (i : I) :
    letI := (universalSpecialization a).toAlgebra
    ChartRing (UniversalBase I) i →ₐ[UniversalBase I] ChartRing R i := by
  letI := (universalSpecialization a).toAlgebra
  exact MvPolynomial.mapAlgHom (Algebra.ofId (UniversalBase I) R)

end SerrePositivity.KST.DerivedBlowup
