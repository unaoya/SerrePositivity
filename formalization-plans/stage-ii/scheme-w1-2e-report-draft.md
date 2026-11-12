# SC-W1 段 2e：停止点報告の下書き（未検収）

2026-11-12 09:50 の依頼により作成。**停止点 2e に達したという報告ではない。** ビルド・監査は 10:02 の合図で再開済み。実装中と下書きの結果は検証済みとして数えない。停止点でこの文書を更新し、未完の項目がなくなったことを調整役が確認できる形にする。

## 1. 対象と検証の境界

BS17 Thm 4.1(i) の経路に必要な、射影の場合の有限性・Rees の核と像の評価・形式関数の **Čech 版**が対象。一般の固有射の有限性、Stein 分解、K 用の段 2c、導来関手の層コホモロジーとの比較は範囲に含めない。

直近の検証済み数学コミットは **`df7c1d105`**（固定した有限被覆の Čech 複体・H と filtered colimit の自然な比較、実際の局所化と余極限、指定部分加群と R/P を分けた次数成分の構成）。対象と直接 importer のビルドは **4,352 jobs で成功**。別実行の標準監査は **7,466 宣言・標準三公理のみ**。8 モジュール・43 件の数学宣言を追加した。前の `72c7ff525`・`8e896e65c` は計 10 モジュール・53 件で、実際の Frobenius と閉厚化・I 進系・形式関数の同型との可換性を検証した。各主張は `scheme-w1-2e-route.md` の各束に一行ずつ記録した。旧来の R/J のテンソル表示との照合は `5d5943541`、実際の flat Čech 比較と加群写像への自然性は `ffac3c764`。KL-W1 の追従で main `0f30e1f6c` を `2ed2c017c` に取り込み、68 本の意味参照を採取した結果、保留 0・書き換え 0 本だった。追従報告は `053bbf1b7`。

指定次数のテンソル局所化・係数環変更・各標準開・図式全体の比較は `1b359a90e` にコミット済み。前の whnf timeout は成分の同型と純テンソル公式への分割で解消した。計算量上限は増やしていない。

調整役の 10:02 の合図でビルド・監査を再開し、実際の Frobenius から閉厚化・互換族・形式関数への接続を検証した。上の監査数に未検証の下書きは含めない。`scheme-drafts/` にある残りの下書きも、検証済みとして数えない。

### 規模の途中報告（11-12 夜の新規則）

段 0 の見込み 8,000–25,000 行に対し、報告点を 12,500 行、停止基準を **50,000 行**として扱う。`0e0f9fc07` での検証済み本体は **205 本・22,140 行**、入口登録を含め **22,346 行**。文書・下書き・他レーンのソースは含めない。残りは約 **8,000–19,000 行**、合計約 **30,000–42,000 行**と見込む。主な幅は共通アフィン細分の正次数の H の比較にある。半分の報告点を越えたので一度報告し、停止せず継続する。50,000 行を超えそうになったら、検証済みをコミットして報告し止める。内訳と計測法は `scheme-w1-2e-route.md` の末尾。

## 2. 射影有限性と形式関数の出力

実装済みの核となる入口は次のとおり。宣言の全一覧と各主張は `scheme-w1-2e-route.md` の各束の表に記録している。停止点では、最終コミットからの宣言一覧を再照合し、この文書または別紙に集約する。ここでは未検証の下書きをその一覧に混ぜない。

| 宣言 | 出力・用途 |
|---|---|
| `projectiveNatGradedFullCechHomology_finite` | Noether 基底上の有限生成次数付き多項式加群の各捻り・次数の Čech H の有限生成性。 |
| `reesAdicProjectiveCechImageRees_finite` | 各 IⁿM の Čech H の像を合わせた Rees 加群の有限性。 |
| `reesAdicProjectiveCechImage_bound`、`reesAdicProjectiveCechImage_cofinal` | 元のコホモロジーの I 進フィルトレーションと、Rees の像のフィルトレーションの比較。 |
| `reesAdicProjectiveClosedCechProjection_shifted_kernel_bound` | 厚化への制限の核を I の冪で評価する。 |
| `reesAdicProjectiveClosedCechTransition_range_stabilizes` | 実際の閉厚化間の Čech H の像が元の H からの像へ安定する。 |
| `reesAdicProjectiveClosedCechCompletionLinearEquiv` | canonical な完備化写像を、実際の閉厚化の Čech H の互換族との同型にする。 |
| `reesClosedCoefficientAdicCechFormalFunctions_module_naturality` | R/J 表示を含む形式関数の比較を、元の次数付き加群の射に自然にする。 |

Rees 次数を移す作用を固定した次数の加群のスカラー作用と混同しない。像の有限性・核の評価・像の安定化を使い、高い I の作用が零であることだけから各 H^q(IⁿM) の零化を導かない。

## 3. §9 の五つの比較の到達点

| 比較 | 現在の検証済み部分 | 未完・下書き | 停止点で必要な証拠 |
|---|---|---|---|
| 共通アフィン細分 | 有界な狭義増加版と全タプル版の Čech 比較、B1 の二重 Čech の増大完全性の API。 | 任意の二つの有限アフィン被覆の共通細分について、係数の射に自然な各 H の比較。 | 実際のアフィン交叉の二重図式、交叉上の完全性、全複体への二つの比較とその自然性。B1 の完全性の同値だけを正次数の H の同型と読み替えない。 |
| 底変換 | `1b359a90e`・`ffac3c764` により、実際の指定次数の標準開図式との自然同型、Čech H の flat 比較、元の次数付き加群の射への自然性まで検証済み。変更先 B の Noether 性なしの有限性も供給。 | 共通細分・Frobenius・実際の近似図式との整合性は、それぞれの未完の群で確認する。 | `projectiveTensorChartDiagramIso`、`projectiveNativeTensorCechIso`、`projectiveNativeTensorCechIso_naturality` が具体的な入口。H とテンソル積の交換には flat を要求する。 |
| 閉厚化 | `5d5943541` の R/J テンソル表示との比較に加え、`72c7ff525`・`8e896e65c` で実際の環の商の表示を比較した。Rees の商の射影・厚化間の遷移と、標準開図式・Čech H の具体的な比較が可換であることも検証済み。 | 共通細分・filtered colimit との整合性は、それぞれの未完の群で確認する。指数を移す Frobenius の厚化間の因子写像は、同じ n の閉厚化の Frobenius と区別し、2f の冪による因子分解に接続する。 | `reesClosedTensorChartIso_naturality`、`reesClosedTensorCechIso_naturality`、`reesClosedRingCechIso_projection`、`reesClosedRingCechIso_transition`。二つの閉厚化の表示の比較であり、非 flat な H とテンソル積の交換ではない。 |
| Frobenius | `72c7ff525`・`8e896e65c` で、実際の局所化・標準開・Čech H の Frobenius と代数の射への自然性を検証した。H 自身の I 進商での n→p*n の遷移と完備化、同じ n の実際の閉厚化の H の Frobenius、既存の射影・I 進遷移・互換族・形式関数の同型との可換性も検証済み。 | 共通細分・底変換・filtered colimit の比較同士の整合性は残る。H 自身の I 進商の n→p*n の写像から、厚化の H の間で指数を移す写像まで得たとはしない。 | `projectiveNatGradedCechFrobenius_naturality`、`reesAdicProjectiveClosedCechFrobenius_projection`、`reesAdicProjectiveClosedCechFrobenius_transition`、`reesAdicProjectiveClosedCechCompletionLinearEquiv_frobenius`。空の標準開と零環を含む。 |
| filtered colimit | `df7c1d105` で、固定した有限被覆の各項・Čech 複体・各次数の H と filtered colimit の比較、および係数図式の射への自然性を検証した。実際の局所化の分数を保つ比較・自然性、指定部分加群の余極限の同定、R と P を分けた次数成分の代表元と分母倍の条件も供給。最終の増大完全性は B1 の `isCechExact_colimit` を再利用する。 | 余極限の次数成分を分子族とする斉次局所化と、有限段の斉次局所化の colimit の同型。実際の標準開の制限・負の次数の零延長・動く基底の係数変更図式への接続と、既存の比較との整合性。 | `projectiveCechFilteredHomologyIso_naturality`、`projectiveLocalizedColimitIso_fraction`、`projectiveLocalizedColimitIso_naturality`、`projectiveFilteredSubmoduleColimitEquiv`、`mem_projectiveGradedColimitGrade_iff`。固定係数の任意の図式の H の比較だけで動く基底の標準開の比較が完了したとはしない。完備化や無限積との交換は使わない。 |

**この表の未完欄が残る限り、停止点 2e の完成とは報告しない。** 新しい比較の図式が既存の R/J・I 進の自然性と同じ実際の写像を使うことも、検証項目に含める。

## 4. 案 (b) の条件と、原典の Hⁱ

[方針の正本](scheme-w1.md) は §9。以下を停止点で再確認する。

1. **「Čech 版」の明記。** コホモロジーの主張は名前に `Cech` を含め、docstring に原典の Hⁱ の番号と、「分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない」を書く。既存の主要な有限性・Rees の評価・形式関数の入口はこの形。追加する比較も同じ条件で確認する。
2. **被覆によらないこと。** §3 の共通アフィン細分の比較を完成させ、係数の射との自然性を示す。標準被覆を一つ選んで計算が通っただけでは、この条件を満たしたとは数えない。現在は未完。
3. **五つの比較が射に自然であること。** 底変換と閉厚化は実際の加群の射、Frobenius は実際の半線形写像、filtered colimit は近似の遷移写像から作る。自然性を結論として証明し、比較同型の存在を仮定に加えるだけにはしない。
4. **最終出力の型。** このレーンの出口は `SerrePositivity.Cech.AugmentedRingCechExact`。それ自体は affine の構造層の増大 Čech 余脈体の完全性で、途中の Hⁱ の定義の置き換えではない。利用側の型も変えない。現状、この束は出口の定義を編集していない。停止点で main との差と利用側を再確認する。
5. **宇宙。** 有限生成の加群には `Module.Finite.small` と `Shrink.linearEquiv` による移送を使える。多項式環と同じ宇宙の加群で計算したことを一般性の制限にしない。実際に大きい型の入口を追加する箇所では、その移送を明示する。

原典の主張は Čech だけで述べられているわけではない。[BST13 Lemma 3.9](https://arxiv.org/pdf/1307.3763v3#page=12) は Nisnevich の導来大域切断、[BS17 Lemma 4.6(i)](https://arxiv.org/pdf/1507.06490#page=16) は fppf の導来大域切断を使う。Stacks の有限性・形式関数も層コホモロジーの Hⁱ。Stacks 30.2.6 のアフィン被覆の比較だけを、Nisnevich・fppf の全ての比較を形式化した証拠としない。承認された案 (b) では、必要な射影の場合の議論を Čech 版で最終出力まで直接つなぎ、これらの導来関手との比較は作らない。

## 5. 検証と宣言一覧の記入欄

停止点で以下を実行・記入する。現在は予定であり、実行済みとは数えない。

- 最終の数学コミット、登録した全モジュール、各数学宣言と主張を一行ずつ。
- 触った対象と直接 importer のビルド結果。共有鍵 `scripts/refactor/with_build_lock.sh --wait 3600` を一回の実行ごとに返す。
- 別実行の `scripts/audit_kst_scheme_lemmas.lean` の宣言数と公理。
- `sorry`・`admit`・新しい公理・既存の宣言の変更・計算量上限の追加の確認。
- 五つの比較とその自然性の具体的な宣言名。証明メモだけを検証結果としない。
- 最終出力と利用側の型の比較、宇宙の入口、下書きのうち本体に採用しなかったものの記録。

ルート全体と下流のビルド・main への取り込みは調整役が行う。

## 6. 2f の入口

[2f の段取り](scheme-w1-2f-route.md) に、型の案、2e の出力との依存関係、不足する補題と規模を記録した。2e の検収後は Frobenius 順極限・nil 不変性・有限射の導手の計算から入る。H⁰ の実際の等化子部分環と、B/IB→H⁰(E) の Frobenius による比較が次の主要な接続になる。一般の固有射の有限性・Stein 分解・Kollár の商は作らない。
