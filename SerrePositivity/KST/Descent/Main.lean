module

public import SerrePositivity.KST.Descent.Axioms
public import SerrePositivity.KST.Descent.MainAugmentedTot
public import SerrePositivity.KST.Descent.Theorem31
public import SerrePositivity.KST.Descent.FiniteZariskiCover
public import SerrePositivity.KST.Descent.FiniteZariskiBaseChange
public import SerrePositivity.KST.Descent.PresheafBaseChange
public import SerrePositivity.KST.Descent.GeneralSplitBaseChangeDescent
public import SerrePositivity.KST.Descent.CentralKernelNaturality

/-!
## 概要
正本 §13 決定 15 の、模型圏側の条件付き結果を使わない L8 主経路。
## 方針
既存の幾何・全次数比較と、以後の L9 の実 Tot による指定比較をここに集約する。
## 規約
最小公理 (1)–(8) の構造体と定理 3.1 全体は構築途中。条件付き補助は import しない。
## 使われ方
論文 §3、定理 3.1・補題 3.2・3.3、(3.6)・(3.8) の主経路の入口。
原典の τ 位相の層論を実 Tot と Čech 計算で置換する。
-/
