# 論文の層の一般論の切り出し（2026-10-28 新設、計画のみ・未着手）

概要：論文の層（CommutativeAlgebra・HomologicalAlgebra・PerfectComplex・KTheory・CategoryTheory・FieldTheory・IntersectionMultiplicity など）には、
Mathlib にまだない一般論が多く含まれている。それらを再利用できるライブラリとして切り出すか、Mathlib へ提出する。
方針：∞ 圏基盤の R レーンとは別に扱う。当面の目標は ∞ 基盤の整備なので、本計画は**着手しない**（ユーザー決定 10-28）。
着手するのは第 I 段の後、または論文の層を触る必要が生じたとき。
規約：数学的内容・公開名・型は保存する。Mathlib へ提出するときは `SerrePositivity` 名前空間を外して改名する。
使われ方：候補の詳細は [全体調査 §6・§7](archive/repository-survey-2026-10-28.md) を参照。本ファイルは候補と前提条件の一覧だけを持つ。

## 1. 候補（費用対効果の順）

| # | 候補 | 規模 | 前提 |
| --- | --- | --- | --- |
| P1 | Auslander–Buchsbaum（HA/AuslanderBuchsbaum） | 1 本・約 400 行 | なし |
| P2 | `TriangulatedK0`・`TStructureHeart`（heart は abelian、Mathlib の TODO） | 各約 140 行 | なし |
| P3 | Koszul 複体の中核（CA/Koszul・KoszulResolution）（Mathlib の TODO） | 約 900 行 | なし |
| P4 | 三角圏の Karoubi 完備化・Verdier t 構造（CategoryTheory） | 約 1,000 行 | なし |
| P5 | 正則局所環・局所平坦性判定・adic 完備化・剰余体の拡大 | 約 100 本 | `RegularLocalRing.lean` → IntersectionMultiplicity の import を切る |
| P6 | Hilbert–Samuel・次元定理 | 約 3,000 行 | `MultiplicityFormulas` の LengthAlgebra・IM 依存を切る |
| P7 | p 基底・Cohen–Gabber・係数体 | 閉包は約 12,000 行 | なし（大きい） |
| P8 | 局所コホモロジー・導来完備化 | 100 本 | BS セッションと調整する |
| P9 | supported K₀・G₀・dévissage・Adams・χ の消滅（Roberts／Gillet–Soulé） | 閉包は約 40,000 行 | PerfectComplex↔KTheory の循環の解消、LengthAlgebra の逆向き import の解消、`K0Supported` と `K0WithSupport` の統一 |

## 2. 整理（切り出しの前に行うもの）

- Paper/ に紛れている一般の補題を移す：
  - Section2 の PerfectApproximation・PerfectTower・PerfectConductor・PerfectBaseChange・TowerApproximation。
  - Section5 の PrimeReduction・ParameterQuotient・Core・GaloisNormalization の一般補題。
  - Asymptotic/NormalizedLimit。
- 名前空間：CA/RootTower と LengthAlgebra/RootTowerLength の `Section2` を `RootTower` に改める。Asymptotic の `paper*` で始まる名前（約 100 個）を一般の名前に改める。
- 第 II 段との関係：`theorem_3_1_K0` を KST から導くための perfect 複体・K₀ の橋（全体調査 §7 の #4・#5）は、∞ 基盤側の計画で扱う。
