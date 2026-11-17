# SC-W1 2h：完全な元の環のČechへの出口

2026-11-17、math/scheme。2g-2の停止点は数学cc1d70c10・報告6f1996722、実測23,945行。指示書末尾の事前承認に従い、2hを別枠1,200行で進める。型の正本は105署名の紙のH01〜H04・16署名、最終出力はdrafts/A6/ArcSheafProperty.leanのG-A6-1aと同じ量化・述語を保持する。

## 途中の到達点（aad26bad8・429ecf3d8）

- H01a〜H01hをPerfectFrobeniusDirectLimitに実装した。元のp乗環準同型の逆の冪を各有限段に置き、同じ順極限の普遍性で元の環への写像を作る。逆は元の段0の射。両側の逆の法則と元の全ての環準同型への自然性を示した。pの像が零という仮定を使い、零環を除外しない。
- H02aは既存の `frobeniusAugmentedRingCoefficientsIso` をそのまま用い、新規本体0行。H02b・H02cはH01の同じ自然な同型をArrowと実際の増大conerveへ送る。H03aは2g-2のaffineVCover_frobeniusCechExactを同じ元の完全環の射のconerveへ移す。
- 本体149＋54行、入口4行、**実測207行**。2g-2との境界はcc1d70c10から数える。所有新規32宣言（生成補助宣言を含む）の公理閉包は標準三公理のみ。各原稿の検証、原稿と本体の同一バイト・SHA、対象と直接importerのビルド（5,413・5,414ジョブ）、別の共有鍵の所有監査に成功した。
- 途中規模報告：残るH04の下書き69行を含め、修正の係数2と登録の予備を確保した完成見込みは約280〜400行。外枠1,200行以内。公開署名・仮定・範囲の変更、一覧への追加はない。引き続きH04と利用側の型の一致の検証へ進む。
- **一覧：済み3／全体4（うち追加0）。内部署名：済み12／16（H02aは既存宣言の利用を含む）。**

## 検証済みの宣言と主張

| ID | 宣言 | 主張 | 本体 |
| --- | --- | --- | --- |
| H01a | `perfectFrobeniusStageMap` | 元のp乗の逆のn乗を有限段の写像とする | PerfectFrobeniusDirectLimit |
| H01b | `perfectFrobeniusStageMap_zero` | 段0は元の環の恒等射 | 同上 |
| H01c | `perfectFrobeniusStageMap_succ_comp` | 元の一段のp乗の遷移を打ち消す | 同上 |
| H01d | `perfectFrobeniusLimitMap` | 同じ順極限から元の環への環準同型 | 同上 |
| H01e | `perfectFrobeniusLimitMap_comp_of` | 各有限段との合成は指定した逆の冪 | 同上 |
| H01f | `perfectFrobeniusLimitEquiv` | 同じ写像を、元の段0への射を逆とする環同型にする | 同上 |
| H01g | `perfectFrobeniusLimitEquiv_comp_of_zero` | 同型と元の段0の射の合成は恒等射 | 同上 |
| H01h | `perfectFrobeniusLimitEquiv_naturality` | 元の環準同型と同じFrobenius順極限の射に自然 | 同上 |
| H02a | `frobeniusAugmentedRingCoefficientsIso` | 既存のχ、係数のFrobeniusと増大conerveの比較 | 既存本体を変更せず利用 |
| H02b | `perfectFrobeniusOriginalArrowIso` | 同じ元の矢印への自然な同型 | PerfectFrobeniusCechComparison |
| H02c | `perfectFrobeniusOriginalCechIso` | 同じ元の増大conerveへの自然な同型 | 同上 |
| H03a | `perfectAffineVCover_cechExact` | 元の一射の完全なaffine v被覆のČech完全性 | 同上 |

全てSerrePositivity.AlgebraicGeometryの宣言。各完全な型はscheme-w1-2g-2-residual-lemma-plan.mdの同じIDにある。H04は検証待ちで、この報告時点では最終出口を完成済みとは数えない。root・下流全ビルドは行っていない。
