module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.ChartAlgebra
public import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
概要：KST §5、Stacks 0815 の有限階数の平坦化に使う Cramer のチャート計算。
方針：置換列の行列式の比で解を作り、チャート元の正則性で係数を打ち消す。
規約：行列式が単元であることは要求しない。
使われ方：行列式中心の blowup チャート上で像加群を自由にする。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
  (I : Ideal R) (a : I) (A : Matrix ι ι R) (hA : A.det = a.1)
  (b : ι → R) (hb : ∀ i, (A.updateCol i b).det ∈ I)

/--
概要：Cramer の分子行列式をチャートの指定した分母で割った係数ベクトル。
方針：全ての置換列の行列式が中心に属するという仮定で比を作る。
規約：KST §5、Stacks 0815、零元を指定する空チャートも含む。
使われ方：像加群の選んだ列による生成。
-/
def chartCramerCoefficients : ι → BlowupChartRing I a :=
  fun i => chartRatio I a ⟨(A.updateCol i b).det, hb i⟩

/--
概要：行列式の像を掛けた係数ベクトルは Cramer の分子ベクトル。
方針：a·(d/a)=d と行列式の環準同型による保存を使う。
規約：KST §5、Stacks 0815、行列式と分母の等式はこの計算に不要。
使われ方：行列方程式の解の構成。
-/
theorem chartCramerCoefficients_smul :
    chartBaseMap I a a.1 • chartCramerCoefficients I a A b hb =
      (A.map (chartBaseMap I a)).cramer (fun i => chartBaseMap I a (b i)) := by
  funext i
  change chartBaseMap I a a.1 * chartRatio I a ⟨(A.updateCol i b).det, hb i⟩ = _
  rw [chartBaseMap_mul_ratio, Matrix.cramer_apply]
  rw [(chartBaseMap I a).map_det]
  congr 1
  exact Matrix.map_updateCol _

set_option backward.isDefEq.respectTransparency false in
include hA in
/--
概要：行列式チャートでは、置換列の全行列式が中心に入る列について行列方程式が解ける。
方針：Cramer の公式を適用して、正則なチャート元を打ち消す。
規約：KST §5、Stacks 0815、行列式は係数環上可逆とは限らない。
使われ方：行列式中心上で選んだ列が像加群を生成する証明。
-/
theorem chartCramerCoefficients_solution :
    (A.map (chartBaseMap I a)).mulVec (chartCramerCoefficients I a A b hb) =
      fun i => chartBaseMap I a (b i) := by
  have hdet : (A.map (chartBaseMap I a)).det = chartBaseMap I a a.1 := by
    exact ((chartBaseMap I a).map_det A).symm.trans (congrArg (chartBaseMap I a) hA)
  have hcalc := congrArg (fun v => (A.map (chartBaseMap I a)).mulVec v)
    (chartCramerCoefficients_smul I a A b hb)
  let : SMulCommClass (BlowupChartRing I a) (BlowupChartRing I a)
      (BlowupChartRing I a) := ⟨fun x y z => mul_left_comm x y z⟩
  rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, hdet] at hcalc
  funext i
  apply (isRegular_iff_mem_nonZeroDivisors.mpr (chartBaseMap_mem_nonZeroDivisors I a)).left
  exact congrFun hcalc i

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
