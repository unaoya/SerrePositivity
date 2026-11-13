
## 停止点 3（C3）

停止点 1 の登録までの `main`（`287fb6e70`）を `math/bs-impl` に取り込んだ。Lemma 10.12、普遍同相、有限エタール代数の perfectoid 性は既存の宣言を用いる。層別の条件はそのまま接続できるので、段 2 の包装は省いた。

| 部品 | 本体で確かめた型と証明 |
| --- | --- |
| G-A8-3′ | `Almost/FiniteEtaleComparison`。分裂後の局所化で二つの像が生成する比較環を、各成分で元の代数の像を取った直積として記述した。有限性、二つの射の整性と局所化での全単射、比較環の導来 p 完備性を証明した。完備性には有限個の分母を払う操作と、完備加群からの全射と完備加群への単射による漸化式の判定を使った。 |
| G-A8-3″・10 | `Derived/IntegralClosureCompletion`。既存の付値環への一意延長を `ArcOutside` に接続した。被約化の主局所化内の整閉包への比較は整で、整閉包とその完備化の両方への比較が `ArcOutside` を満たす。有限エタール層の平坦性で p 冪ねじれの境界を移し、導来完備化の離散性と通常完備化への単位付き同型を得た。 |
| G-A8-8 | `Derived/PerfectoidFilteredColimit`。小さい filtered 圏を Mathlib の共終な有向半順序で置き換え、一段以降で最小元を取った。元とその等式の段への降下で指定余極限を環の有向余極限と比較し、完備化の perfectoid 性、p 冪ねじれの境界、導来完備化の離散性を証明した。 |
| G-A8-9・11 | `Derived/IntegralApproximation` と `Derived/IntegralClosureApproximation`。有限個の変数と関係に各変数のモニック関係を加えた小さい有向図式を作った。G-A8-11 では局所化先の生成元と核の関係の分母を払い、指定局所化が全単射になる段を共終に取った。整閉包への特殊化では、有限エタール層の各元が基底の局所化上整であることから、分母を払って整閉包に入れた。 |

登録候補は次の五モジュール。

- `SerrePositivity.BhattScholze.Almost.FiniteEtaleComparison`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralClosureCompletion`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.PerfectoidFilteredColimit`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralApproximation`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.IntegralClosureApproximation`

共有鍵付きの対象ビルドに成功。新規モジュールを対象とした段階 II と同方式の監査は 171 宣言、標準三公理のみ。本体の既存宣言の変更と新規の `sorry` は 0。⑤b・⑥ とファイルの重複はなく、入口と共通の監査は調整役の登録に委ねる。
