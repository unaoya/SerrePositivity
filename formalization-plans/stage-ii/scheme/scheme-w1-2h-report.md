# SC-W1 2h：完全な元の環のČechへの出口

2026-11-17、math/scheme。2g-2の停止点は数学cc1d70c10・報告6f1996722、実測23,945行。指示書末尾の事前承認に従い、2hを別枠1,200行で進める。型の正本は105署名の紙のH01〜H04・16署名、最終出力はdrafts/A6/ArcSheafProperty.leanのG-A6-1aと同じ量化・述語を保持する。

## 途中の到達点（履歴：aad26bad8・429ecf3d8）

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

全てSerrePositivity.AlgebraicGeometryの宣言。各完全な型はscheme-w1-2g-2-residual-lemma-plan.mdの同じIDにある。上記の途中報告の時点ではH04は検証待ちだった。以下の完成報告で閉じた。root・下流全ビルドは行っていない。


## 停止点2h：完成（2026-11-17、数学7971aefe8）

**一覧：済み4／全体4（うち追加0）。内部署名：済み16／全体16。** H02aは既存宣言の利用で、本体を変更していない。最終型・量化・零環・空の有限族の扱いは計画どおり。

| ID | 宣言 | 主張 | 場所 |
| --- | --- | --- | --- |
| H04a | `finitePi_primeCast_eq_zero` | 各係数でp=0なら同じ積でもp=0 | PerfectAffineVCoverCech.lean:20 |
| H04b | `finitePi_primePower_bijective` | 各係数のp乗の全単射性から同じ積の全単射性 | 同:27 |
| H04c | `perfectRing_primePower_bijective` | PerfectRingの全単射性を指定したp乗の環準同型へ渡す | 同:44 |
| H04d | `cech_exact_of_vCover_perfect` | 完全F_p代数の有限族のv被覆の元の増大Čech完全性 | 同:51 |

本体の3ファイルは SerrePositivity/AlgebraicGeometry/PerfectFrobeniusDirectLimit.lean、PerfectFrobeniusCechComparison.lean、PerfectAffineVCoverCech.lean。入口 SerrePositivity/AlgebraicGeometry.lean に全て登録済み。本体149＋54＋69＝272行、入口6行、**追加実測278行／外枠1,200行**（基準cc1d70c10、削除の相殺なし）。検証済み数学のコミットはaad26bad8・429ecf3d8・7971aefe8。

### 検証

- 原稿の `lake env lean`、原稿と本体の同一バイト・SHA、本体3モジュールと直接のimporterの対象ビルドが成功。最終対象ビルドは5,415ジョブで成功。既存依存はキャッシュを利用し、rootは実行していない。
- 各束ごとに別の共有鍵で、private・生成宣言を含めた所有宣言の公理閉包を検査。H01は20件、H02/H03は12件、H04は4件、**合計36宣言、標準三公理（propext・Classical.choice・Quot.sound）のみ**。sorry・新しいaxiom・native_decideはない。
- 正本 ArcRouteB.lean の定義だけをコピーした小さい検証で、次の項を型検査した（draft全体をビルドしたという主張ではない）。

```lean
example (p : ℕ) [Fact p.Prime] : BS17VCechInput.{u} p := by
  intro A _ _ _ ι _ B _ _ _ f hf
  exact SerrePositivity.AlgebraicGeometry.cech_exact_of_vCover_perfect p B f hf
```

- ArcSheafProperty.lean の元の AugmentedRingCechExact の定義も同じ検証へコピーし、本体Cech.AugmentedRingCechExactとの同値を `Iff.rfl` で検証した。最終出力の型を置き換えていない。最初の検証は無関係なB1〜B5の未復元oleanをimportして失敗したため、そのimportを除き、2h本体のみで定義の照合を再実行して成功した。
- 証跡はworktreeの formalization-plans/stage-ii/scheme-drafts/ の2h-H01/H02H03/H04各log、manifest、2h-ArcRouteBInput-check-2.log。鍵は --class impl --wait 3600、一回のビルドまたは監査ごとに解放した。

### 範囲と次の段

BS17 Thm 4.1(i) の n=1・E=O・affine・完全F_p代数の有限族の範囲。一般W_n・有限射影E・非affineのv位相は作っていない。中間の射影的コホモロジーは承認されたČech版で、導来関手Hとの比較を形式化したという主張ではない。

指示書末尾の事前承認に従い、ここで取り込み待ちをせず **2iの段0の紙のみ**へ進む。その提出後は指示書の明示的な停止点で止まり、2iのLeanは始めない。取り込み・rootと下流の全ビルドは調整役が行う。
