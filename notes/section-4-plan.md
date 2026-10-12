# §4と二つの実現の入力境界

2026-10-12 更新。現在状態の正本は [status.md](status.md)、作業規約は [PLAN.md](PLAN.md)。
抽象化・二つの実現・λ平坦性／λCM性からの接続は完了した。
主定理への具体的接続も名前付き入力に相対的に完了し、追加の存在構成を残作業とはしない。
降下の二つの保留定理の証明は引き続き別課題である。

## 仮定確認と適用先

| 付録の確認項目 | 入力として指定するもの | 実現側で証明するもの・主な入口 |
| --- | --- | --- |
| perfect：支持 | 有界有限射影複体とホモロジーの幾何学的支持 | スカラーの冪の零作用との同値。`PerfectComplex/Support.lean`・`HomotopyCategory.lean`。任意の可換環で成立 |
| perfect：有限 Euler 評価 | `J.FG`、支持イデアルの根基への包含、全ての正の冪の `KoszulFinite` | 各ホモロジーの冪ねじれ性・有限性、商値のホモロジー関手、シフト・有界性、旧 Euler 数との一致。`LengthAlgebra/PerfectHomology.lean` |
| perfect：二つの商の一致 | 上と同じ有限性条件 | `FiniteQuotientEquivalence`・`PerfectHomologyComparison` が有限商と大きな商の有限部分を同定し、長さ・零対象・Euler・K₀ 評価を一致させる |
| perfect：消滅 | 指定したスカラーの零ホモトピー、項の振幅、環自身の高次 Koszul ホモロジーの長さ零 | 有限射影項のフィルトレーションで (Kosₘ) を確認し、反復錐から消滅。`lambdaHomology_projective_vanishing` は Koszul 有限性を使わない |
| perfect：下界 | Euler の有限性、振幅 `[-e,0]`、零次の全射。具体的な全射には微分の極小性・零次項の基底を指定 | 消滅・第零次同型と全射の長さの単調性。極小性からの全射も `PerfectMinimalLowerBound` で構成し、他の項に自由性は要求しない |
| 共通：基底公式 | Noether 局所基底、`(z)=m`、`IsKoszulResolution z`、係数側の Koszul 有限性 | `KoszulFormula` により係数 `eλ(z;C)` の公式。高次消滅や `eλ=rank` はこの一般公式の仮定にしない |
| 共通：対称な比較 | 二つの Koszul Euler 数の一致、評価元の K₀ の有限群作用、不変類の整数倍の降下 | `perfectEuler_conjSum_eq`・`symmetricPaperEuler_conjSum_eq`。群論の `conjSum_eq` を共有し、係数環への群作用や長さの不変性は要求しない |
| perfect：旧群作用・降下の接続 | 支持パラメータを固定する環の群作用。降下の移送には係数環の局所性と旧 K₀ の降下 | `K0Functoriality` が実際の作用を構成し、K₀ 比較の同変性・係数変更との可換性から降下を移送する。任意の環で比較写像が同型とは主張しない |
| ランク：評価先と局所化 | 正の基準列 `s`、`atTop` に沿う超フィルター、長さ・根基条件・Koszul 有限性 | `SequenceHomologyBounds` が有限性と `O(s)`・`o(s)` を証明。`SequenceHomologyLocalization` が分母の可逆化とホモロジー的関手を構成 |
| ランク：完備化・有界性 | 上の入力と実際のランク商 | `CompletedHomology`・`RankHomologyShiftNatural`・`CompletedRankEvaluation` が冪等完備化への延長、自然なシフト比較、対象ごとの有界性、共通 Euler 評価を与える |
| ランク：全対象での基底公式 | 上記の基底の Koszul 分解 | `supportedRank_isIdempotentComplete_of_koszul` により一様な代表へ帰着し、各段の有限版公式を正規化極限へ移す。`koszulPaperEulerK0_changeRing` はランク K₀ 全体が一つの Koszul 類で生成されるとは仮定しない |
| ランク：消滅 | 商での支持・スカラーの零作用、共通振幅、各段の Koszul 消滅 | `RankVanishing`・`PaperVanishing` が (Kosₘ) と反復錐を接続。元の複体列の一様支持は不要で、Koszul を掛けた列の一様支持を証明して使う |
| ランク：下界 | 上記と微分の極小性、パラメータの冪を含むイデアル | `RankMinimalLowerBound`・`PaperMinimalLowerBound` が第零次全射と正規化極限の単調性から階数の極限による下界を得る |
| §5：有限近似からの正値性 | 有限近似の長さの収束、一様な消去イデアル、係数側の正の商長さなど | `paperEuler_pos_of_finiteApproximation` などが生成元数の正の極限を導き、上記の下界を適用。元の素イデアル商からの存在構成は `Section5/Core` で引用に相対的に接続済み |


基底のKoszul分解を明示する一般比較に未証明入力はない。
正則局所環から分解を供給する正則パラメータ定理も証明済み。
有限自由／有限射影K₀の比較同型は局所環上で使い、任意の環では比較写像だけを使う。

## 実装と履歴

共通比較は `perfectEuler_conjSum_eq` と `symmetricPaperEuler_conjSum_eq`。
具体的なLemma 3.5は `theorem_3_1_K0`、定理4.7は
`Section4.supportedRankK0_descent` を適用し、`sorryAx` が残る。
反復錐は再帰的な二項直和表示を使う。並べ替え同型と `ι` の独立入口は追加しない。

- [旧計画と実装記録](history/section-4-plan-through-7c3fc2c.md)
- [t構造の実施記録](history/section-4-tstructure-progress-through-7c3fc2c.md)
- [数学的な代替証明](section-4-devissage.md)
- [2026-10-11の削除記録](cleanup-candidates-2026-10-11.md)
