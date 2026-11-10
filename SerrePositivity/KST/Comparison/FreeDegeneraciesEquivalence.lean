module

public import SerrePositivity.KST.Comparison.FreeDegeneraciesColimits
public import SerrePositivity.KST.Comparison.FreeStandardContraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.CellularNaturalComparison
public import Mathlib.Tactic.CrossRefAttribute

/-!
# 自由な退化の augmentation の局所化可逆性

概要：自由な退化から元の単体集合への自然な射は、全ての単体集合で局所化同型。
方針：余極限・単射保存と標準単体の実際の収縮からセルに関する帰納を適用する。
規約：Segal 1974 Proposition 1.6 の fat realization と対角の模型比較の補助。
使われ方：二重単体集合の各列への自由な退化の適用。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory
open SerrePositivity.SimplicialModel

/--
概要：自由な退化の augmentation は任意の単体集合で局所化同型である。
方針：各標準単体の収縮を、余極限と単射の保存により全てのセルへ移す。
規約：値宇宙のモデル構造や可逆性の追加仮定は置かない。
使われ方：自由な退化の各列の対角への比較。
-/
@[kerodon 0124]
theorem freeDegeneraciesAugmentation_localized_isIso (X : SSet.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (freeDegeneraciesAugmentation.app X)) :=
  CellularNaturalComparison.app_isIso freeDegeneraciesAugmentation
    freeDegeneraciesAugmentation_standard_localized_isIso X

end SerrePositivity.KST.Comparison
