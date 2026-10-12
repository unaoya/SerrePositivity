# §2の実装対応と入力境界

2026-10-12 更新。現在状態と引用一覧は [status.md](status.md) が正本。
主張・文献との照合は [section-2.md](section-2.md) を参照。

## 現在の到達点

| 部分 | 実装と境界 |
| --- | --- |
| Lemma 2.1・2.2 | 剰余体拡大・二つのCohen正規化を引用し、保存則と適用条件を証明 |
| 塔・長さ | 単項式基底、段、有限段公式、降下、上限性を証明。長さの二性質だけ引用 |
| 等標数 | perfection・Frobenius・有向ホモロジー・長さ極限をRoberts引用へ接続 |
| 混標数 | 完備塔・perfectoidizationを構成し、Bhatt–Scholze／CLMST引用へ接続 |
| 定理2.5 | 両標数の構成から証明。構成の接続に直接 `sorry` はない |
| 標準可換環論 | Samuel多項式性、次元、正則パラメータ、非混合性、Koszul重複度、パラメータの冪は証明済み |
| 系2.6 | 上限性・組成列・証明済みの重複度正値性を適用 |

## 重複度の証明を追う順序

`KoszulReesFinite` → `GradedKoszul`／`GradedKoszulVanishing` →
`ReesKoszulEvaluation` → `GradedAdicExactness`／`ReesKoszulAcyclic` →
`AdicEulerComparison` → `KoszulAdicEuler` → `KoszulMultiplicityProof`。

次数付き評価の像・単射性・境界持ち上げは具体的に確認され、最終公式の仮定には残らない。
有限長の数値変換は `FiniteLengthValue`、反復錐と相殺は共通の圏論APIを使う。
任意有限加群への重複度公式の拡張は別課題であり、環自身の公式の未証明箇所ではない。

## 履歴

旧§5などを参照する過去の記録は [旧計画・検証記録](history/section-2-plan-through-7c3fc2c.md) に保存した。
21・20・19・18・17件という `sorry` 集計は当時の記録で、現在の件数ではない。
