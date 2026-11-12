-- BS-W16 段 4。未供給の十八欄の作業用。BS の drafts からは import しない。
module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.Assembly

/-!
# Barratt–Eccles 全界面の残りの入力

## 概要
HA §3.2.2–3.2.4 と DAG XIII Construction 2.2.6 の未供給欄を記録する。

## 方針
本体の barrattEcclesTheoryOfRemaining に残りの欄だけを渡す。
証明済みの欄は、その本体の組み立て関数が固定する。

## 規約
sorry は本作業用ファイルだけに置く。全界面を無条件に構成済みとは扱わない。

## 使われ方
後続の経路 B・③-b の橋・G12・M14 により、残りの入力を順に供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.BarrattEccles

/-- 既証明の欄を固定した、BS-W16 の全実例の残り。 -/
def barrattEcclesTheory : EInfinityTheory.{u} :=
  barrattEcclesTheoryOfRemaining
    (forget_preservesSifted := by sorry) -- HA 3.2.3.1、③-b の橋の後
    (presentable := by sorry) -- G12
    (coproduct_tensor := by sorry) -- HA 3.2.4.7、経路 B の全関手版
    (coproduct_tensor_legs := by sorry) -- 同じ比較が指定二脚を標準射へ送る
    (ofCosimplicial := by sorry) -- G10 の Tot の模型
    (ofCosimplicial_forget := by sorry) -- 同じ Tot と忘却の比較
    (ofCosimplicial_cone := by sorry) -- 指定した native な極限錐
    (ofCosimplicial_restrict := by sorry) -- 係数制限との全関手版の比較
    (ofCosimplicialCdga := by sorry) -- 厳密 cdga の Tot
    (ofCosimplicialCdga_cone := by sorry) -- 同じ cdga の指定錐
    (ofCosimplicialCdga_discrete := by sorry) -- 離散入力との比較
    (ofCosimplicialCdga_evalZero := by sorry) -- 零頂点への評価
    (ofCosimplicialCdga_evalZero_leg := by sorry) -- 同じ指定錐の零頂点の脚
    (toSpectra := by sorry) -- D79：V。まず F_p の実例を構成する。
    (toSpectra_restrict := by sorry) -- 係数を忘れる同じ Sp の比較
    (toSpectra_homologyIso := by sorry) -- 同じ V の自然な π/H 比較
    (powerOp0 := by sorry) -- M14、DAG XIII Construction 2.2.6
    (powerOp0_zero := by sorry) -- 零次の Frobenius
    (powerOp0_pos := by sorry) -- 正次数の消滅
    (powerOp0_discrete := by sorry) -- 離散入力での比較
    (powerOp0_tot := by sorry) -- 同じ Tot に対する比較

end SerrePositivity.EInfinity.BarrattEccles
