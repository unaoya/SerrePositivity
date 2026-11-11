module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ExtendedInputGluing

/-!
概要：二成分の依存族を同じ二点添字上でまとめる。
方針：二点の依存除去を一つの公開補助定義として共有する。
規約：元の二成分を定義的に回収する。
使われ方：実際の二成分の交互構成への接続を小さい検証単位に分ける。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
universe v
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：二点で与えた値から依存族の全切断を作る。
方針：Fin 2 を二度除去する。
規約：零点と一点では元の値に定義的に一致する。
使われ方：元の二成分の全図式と証明の一括入力。 -/
def finitePairSection (P : Fin 2 → Sort v) (a : P 0) (b : P 1) : ∀ c, P c :=
  Fin.cases a (Fin.cases b (fun i ↦ Fin.elim0 i))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
