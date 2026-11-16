# SC-W1 2g-2：20,000行の規模境界（2026-11-17深夜）

> この境界の後、ユーザーが同じ型・範囲で外枠21,000行への拡張と再開を明示的に承認した。Leanの追加・修正の停止は解除済み。以下は境界時点の記録であり、2g-2の完成を意味しない。

## 状況と停止理由

承認済み外枠は20,000行。基準56ea849a3からの検証済み実測は17,611行（新規243モジュール本体17,322、既存追加25、入口264）。数学の先端は **a1ecabce8**。その後のe0753573a・86340faa2・cde5a4bb1は紙のみ。G3は完成、G4・G5は未完で、停止点2g-2ではない。

`coordination.md` §2の「上限を超えそうなときは報告して止める（止まる前に、それまでの検証済みの分をコミット）」および夜の進め方(2)に従う。残りの比較の下書きを具体化したところ、同じ型・範囲での完成見込みが約19,600〜20,500行となった。上端が外枠を超えるので、新しいLeanの追加・修正を止める。既に提出した検証は同じ生存セッションの結果を確認するが、結果がエラーなら未検証の下書きのまま保持する。2hの段0を紙で更新し、2hのLeanは開始しない。

## 検証済み成果と未検証分

最新の検証済み二本は `SchemePerfectCechTupleLeftTotalDifferential`（131行）と `SchemePerfectCechTupleLeftBaseComponents`（67行）。同じσの微分との可換性と鎖写像、元のleftCの包含・射影の同型、元の基底射影の零次・正次数の式を供給する。直接importerの入口を含む対象ビルドは5,338ジョブ・終了0。別の共有鍵の所有監査は非公開・生成分を含む22宣言（15、7）、標準三公理のみ・終了0。ログはscheme-draftsの `2g-g4-left-differential-native.log` と `2g-g4-left-differential-audit.log`。全新規所有宣言の小監査累計1,883、既存15は別計上。追加公理・sorry・既存宣言の型変更・資源上限の引き上げ・200行超の宣言なし。

次の八本823行は **全て未検証・本体未登録・数学未コミット**。draftsは作業木の `formalization-plans/stage-ii/scheme-drafts/` に保持し、.lakeや/tmpには置かない。

| 下書き | 行数 | 主張／法則 |
| --- | ---: | --- |
| SchemePerfectCechTupleLeftTotalBaseSection | 151 | 元の基底射影の次数ごとの右逆とψσ+Pr=1 |
| SchemePerfectCechTupleLeftTotalShortComplex | 161 | 同じ短複体のSplitting・短完全性、元のLeftKernel.totalと元の増大totalの完全性の同値 |
| CechIntegerTotalVerticalSucc | 53 | 同じ縦一段の再索引のtotalDescが二方向の微分の式から全微分を保つ |
| SchemePerfectCechTupleRightCenterComponents | 115 | 元の右側と中心自身の恒等矢印の左側との符号つきの各脚と逆向きの射 |
| SchemePerfectCechTupleRightCenterRetraction | 100 | 同じ各全次数で二つの比較射は互いに逆 |
| SchemePerfectCechTupleRightCenterVertical | 70 | 元のCの射影の自然性と同じ符号つき比較の縦微分の式 |
| SchemePerfectCechTupleRightCenterHorizontal | 84 | 同じ各余面・退化に自然で、交代和の水平微分を保つ |
| SchemePerfectCechTupleRightCenterTotalIso | 89 | 同じ右側のwhole totalと中心の左側のunsigned successorの同型 |

左側の二本のmodule形式の検証は、最初に局所記法のshow、次に明示的な宇宙指定がquotPrecheckに拒まれた。さらに `BB.X` 等は局所記法へのドット記法にならないため `(BB).X` 等へ直した。これらは記法の修正で、数学の証明が検証されたとは主張しない。固定manifestは `G4LeftShortExactBatch.manifest.json`、再検証の唯一の待機はセッション64564、ログ予定は `2g-g4-left-short-exact-check-3.log`。右側六本は `G4RightCenterBatch.manifest.json` に固定したが、検証待ちは出していない。

## 残りの同じ型と見込み

元のRightKernelのtotalの完全性を、中心の元の増大totalの完全性から得る。同じ実際の基底射影のkernelSequenceと既存のtotalの短完全性を用いる。これに元のF8の条件付き消去を合わせ、同じLeftKernelから元の増大totalへ戻す。中心側の完全性を一般の固有降下の追加仮定として残さない。

| 仕事 | 下端 | 上端 |
| --- | ---: | ---: |
| 既存の未検証八本＋入口八行 | 831 | 831 |
| 元の右側の核への完全性の移送、上の下書きの型・微分の修正と登録 | 120 | 320 |
| 非アフィン中間基底上のproper fppf・合成・nil不変性・固定した固有射のNoether閉像帰納 | 400 | 700 |
| G5：元の模型とFrobenius・二つのfiltered余極限の自然な移送 | 600 | 1,000 |
| 残り合計 | 1,951 | 2,851 |
| 検証済み17,611行との合計 | **19,562** | **20,462** |

丸めて約19,600〜20,500行。前回の19,061〜19,911行からの上振れは、残りの比較を450〜600行と置いた部分が、未検証の八本だけで823行となったことによる。G5は既存のFrobeniusの自然性・MathlibのFubiniの同型で縮む可能性があるが、まだこの実際の模型への代入を検証しておらず、上限に合わせて見込みを切り下げない。型や範囲を狭めたり、長い行への圧縮で外枠を調整したりしない。

Noether帰納の量化は、まず閉像C上の固有全射を固定し、その後全てのNoetherアフィンT→Cでの底変換を扱う。C上で先に選んだ実際のblowupの中心は真に小さい閉像C'で、IH(C')をその中心のTへの底変換へ適用する。T上で新しい中心を選び、そのCへの像が真に小さいと仮定する経路は取らない。相対proper fppfでは非アフィン中間基底のΓの平坦性を仮定せず、元のアフィン交叉・共通細分・B1へつなぐ。

G5は同じ `coefficientVCoverModelSmallArrowDiagram` とそのcolimit、各模型のv判定・有限表示性を使う。既存の `frobeniusArrowSmallDiagramMap`・`frobeniusArrowCocone_map`・`frobeniusArrowSmallColimitIso_naturality` とMathlibの `colimitFlipCompColimIsoColimitCompColim` を再利用し、B1のfiltered完全性へ渡す。新たな模型や別のperfectionを作らず、元のv被覆の `AugmentedRingCechExact (frobeniusAugmentedRingCoefficients …)` まで戻す。これらは未実装の接続であり、最終結論にNoether性・模型・中心の完全性を追加仮定として残さない。

## 判断が要る点

同じ型・範囲のまま **外枠21,000行** への拡張を求める。完成見込み上端20,500行に約500行の余裕を置く案。承認前は新しいLeanの追加・修正をせず、2hの段0の紙までを行う。2hは[段0の§12](scheme-w1-2h-route.md)に更新した。

mainは取り込んでいない。共有鍵は `--class impl --wait 3600`、待ちは一件。root・下流全ビルド・AlgebraicGeometry全体監査は行っていない。取り込みは調整役が行う。

一覧：済み1／全体3（うち追加0）。
