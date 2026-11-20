# IM-W1 段1　旧別名と import 専用ファイルの一覧

現在地は段1の調査完了。枝は `refactor/import-cleanup`。開始時の main は `465d5c7cd`、調査中に共通規則などの文書更新を取り込み、最終基準を `17fdb6570` とした。変更はこの報告と二つの CSV。削除・移動・import の書き換えは段2の承認後に行う。

## A. 旧別名

| 定義ファイル | 行数 | 本体の直接 import | 本体外の直接 import | ファイルの案 |
| --- | ---: | ---: | ---: | --- |
| `Util/DeprecatedAlias.lean` | 106 | 345 | 0 | 廃止候補。命令・拡張を使う側が見つからない |
| `InfinityCategories/Project/SimplicialCombinatorics/DeprecatedAlias.lean` | 105 | 730 | 1 | 回帰試験が使うので残す |

本体の **1,075行・1,075ファイル**を import の整理候補とする。調整役の1,075本に、`scripts/refactor/tests/deprecated_alias.lean:2` の1本を足すと実測の1,076本になる。すべて `public meta import`。root、blueprint、research、Archive からの直接 import は0件。CSVには命令、永続環境拡張 `typeAliases`、その非公開補助と実装内の参照も載せた。命令に対応する生成名は AR-W1 段3の所有元付き表で照合した。二つの実装は既存の deprecated 属性と Batteries の alias 情報を使う。独自の属性登録は0件だった。[Aの一覧](../../../research/import-cleanup/alias-leftovers.csv)

- CF-W1 の13件をすべて現行の回帰ファイルで照合した。構造体・射影・パターン、方程式補題、deprecated の行き先、instance と simp の二重登録、再帰定義のコード生成を検査する。bulk 鍵で `lake env lean scripts/refactor/tests/deprecated_alias.lean` を実行し、終了0。43行の既知の `unusedSimpArgs` が1件。ファイル上限の診断と再試行は0件だった。
- `scripts/refactor/check_deprecated_aliases.lean` は `import Lean` と入力 JSON のモジュールを使う汎用の検査器。13件のコマンドを置いているのは回帰ファイルで、検査器とその Python 試験は維持できる。移動用の `klw1_namespace.py` は今も `deprecated_alias` の文字列を生成する。比較器・計測器の字面の参照は表で区別した。
- 本体・scripts・blueprint・research の追跡 Lean ソースをコメント・文字列と区別して照合した。二つの実装内と回帰ファイルの外に、両命令の呼び出し・永続拡張・旧試験名の参照はなかった。

両定義ファイルが再公開するのは `Mathlib.Util.AliasIn` と `Lean.Compiler.LCNF.PhaseExt`。他の import を固定して一つの行だけを外すと、前者への到達が切れるのは217箇所（本体216、試験1）。残る859箇所の代替経路も、廃止する予定の本体 import を同時に外す場合は再評価が要る。両定義ファイルを閉包から除く感度分析では全1,076箇所で `Mathlib.Util.AliasIn` の到達を失い、`Lean.Compiler.LCNF.PhaseExt` とその他の推移先はたどれる。後者の通常到達と meta の再公開は別なので、段2では要求する入口に直接 import を補って型検査する。前者の `@[alias_in]` は調査対象の有効なソースに呼び出しが見つからなかった。実際に減る import 行数は、その段で必要な付け替えを引いて確定する。定義ファイルの提案は106行・中の import 2行の削除と、105行・中の import 2行の保持。

## B. import 専用ファイル

Archive を除く本体の追跡 Lean 34,208本をソースから読んだ。空白、入れ子コメント、ヘッダの `module`・`prelude`、修飾付き import、対応する `namespace`・`end` を認めた。残りのコマンドを確認し、宣言のない309本の `example`・`#print`・`#check` と2本の局所設定を判別した。追跡パスを AR-W1 段3の所有モジュール表と照合した。ビルドを伴う検査コマンドを持つ本体ファイルも、境界を確認できるよう同じ表に載せた。[Bの一覧](../../../research/import-cleanup/import-only-files.csv)

| 現行ソースの区分 | 消す案 | 残す案 | 判断できない | 合計 |
| --- | ---: | ---: | ---: | ---: |
| import とヘッダ・名前空間のみ。0 import の空ファイル9本を含む | 126 | 98 | 14 | **238** |
| 宣言なし・検査命令あり | 0 | 309 | 0 | 309 |
| 宣言なし・局所設定あり | 0 | 0 | 2 | 2 |
| 合計 | **126** | **407** | **16** | **549** |

| 案 | ファイル内の import 行 | ファイルの全行（コメント・空行を含む） |
| --- | ---: | ---: |
| 消す | 125 | 2,855 |
| 残す | 31,214 | 50,008 |
| 判断できない | 17 | 318 |

**消す案126本。** Rectification の旧パス116本、ほかの移動・統合で正本を再公開するだけの9本、空になった `DifferentialGraded/Checks/Morita/ScalarExtensionAcceptanceChecks.lean` 1本。1 import の旧パスは修飾子を保って正本へ付け替える。たとえば `EInfinity.lean:2077` の `HomologicalAlgebra.Complexes.Limits.ExtendTruncationHom` は `HomologicalAlgebra.ComplexLimits.ExtendTruncationHom` を直接指定する。空の DG 入口は `Checks/Morita/U16Checks.lean:3` と生成監査の import・所有元一覧から除く。正本への切り替えと合わせ、旧 Rectification パスを存在確認する配置監査には、台帳の既存 `direct_relocations` を使う。旧パスの互換終了は段2の承認に含める。

- 直接の修正箇所は51 import 行（本体34、正式監査2、その他スクリプト15）で45ファイル。2件の監査対象名と台帳1ファイルを含め、合計46ファイル・54箇所。台帳の箇所は同じ挿入先に116対応を追加する。調査時点の禁止名の配列は、旧入口が再導入されていないことを検査するため残せる。修正箇所とその他の言及を別の列にした。

**残す案407本。** root 1本、領域・公開入口73本、監査入口23本、`WordSegmentComparison` 1本、検査命令を持つ309本。検査ファイルには `example` 1,281件、`#print` 3,826件、`#check` 56件があった。DG の受け入れ例は対象ビルドで検査される。root や正式監査が使う集約は、既存の入口と監査範囲を維持する。ファイルごとの import 元を CSV に記録した。

### 判断できない16本

- `InfinityCategories/Project/Entrypoints/` の `DwyerKan`、`Exact`、`Infinity`、`Lax`、`Pointed`、`Semiorthogonal`、`Simplicial`、`Verdier`。現在は空で利用箇所もないが、将来の配置先として予約されている。
- 同じ場所の `Kan` と `StablePresentable`。直接の利用は見つからない。将来の領域入口としての説明があり、現行の公開 import はそれぞれ4本と5本ある。
- `HomotopicalAlgebra/Simplicial/` の `SmallKanHomotopy`、`SmallTargetKernelQuotient`、`StarDiagramSmallQuotient`、`WeightedWordHom`。IC-2 §14 が扱う4本。互換台帳と利用を確認した上での Archive という決定があり、今回の削除案から外した。
- `HomologicalAlgebra/` の `CompleteTwoCohomologyAnnihilator` と `IdealPowerTorsionBaseChange`。宣言が移った後も局所設定が残り、root と `scripts/audit/shared.lean` が import する。前者には局所 instance 属性もあるので、import だけの承認に含めず保留した。

### 到達と監査

- 現行の明示 import と正式監査108本のリテラル実行時 import から閉包を作った。本体の到達数は root 29,863、root と正式監査の和34,006。AR-W1 段1の「単独 import」は、root 外で監査1本だけから届くモジュールとして現行で取り直した。単独到達は全体で2,787本、表の中では335本。DG 監査の単独到達は全体で304本と段1の件数に一致し、うち302本が表に載る。残る2本（`Checks/Acceptance`、`Checks/DerivedRing`）は宣言を持つ。
- CSVの `lost_modules_without_rewiring` は、各行のモジュールを外して付け替えをしない場合に到達を失う、**その行自身を除く**本体モジュール。59入口で該当し、重複を除いて9,688本。たとえば `HomotopicalAlgebra/Rectification/Foundations.lean` は root 外の423本への入口で、監査の import を保つ。削除案126本で、到達を失う残存本体モジュールは0。全案を同時に付け替えた場合も、root、正式監査の各108本、blueprint、その他の検査スクリプトで、残す本体モジュールの到達を失うものは0。削除案自身では、空の DG 入口だけが現行の単独監査対象に当たる。
- `lakefile.toml` と `blueprint/lakefile.lean` を別に確認した。表中で Lake が個別に名指しするのは root。blueprint から表への直接 import は0件で、推移到達は列に記録した。宣言表作成器などの外部入力で対象が変わる読み込みは、固定の対象リストと別に扱った。文書・過去の報告の字面は到達や稼働中の参照に数えていない。現在の参照元、名前で指定された監査項目、配置台帳、文書のパス言及は CSV で追える。
- `form_commit` は、現パスで現在の import 専用形または検査形が続き始めたコミット。Git の first-parent と、形を持ち込んだ merge のもう一方を確認した。現パスの追加時点と最終変更も併記した。たとえば Rectification の旧位置は `bb85c5ec1`、∞ の公開入口は `54f6413f6`、空の DG 入口は `024eaa702` の整理に由来する。

到達は静的なモジュール閉包。記法、局所属性、instance 探索、外部利用者、定数の可視性まで保証するには段2の試験が要る。宣言を持つファイルの未使用 import と間接だけの import は今回の判定範囲外。

### 調整役の数との差

| 項目 | 調整役 | 現行の照合 |
| --- | ---: | --- |
| A の直接 import | 約1,075 | 本体1,075＋試験1 |
| B の宣言なし | 550 | 所有元表とソースで549。指定の狭い意味での import 専用は238 |
| B で import 1本 | 357 | 旧550本で本体内の辺だけなら357を再現。外部も含めると207。一行も検査・設定命令を持たない238本では136 |
| B を本体と root のいずれも直接 import しない | 446 | 宣言なし549本では446で一致。import 専用238本に限ると155 |
| `DifferentialGraded/Checks/` の宣言なし | 307 | 307を再現。306本に検査命令があり、空の1本のみ import 専用側 |

調整役の11-20の import 候補集計に使われた `2026-11-20b` のダンプを再集計した。550本に入る `InfinityCategories/Models/EInfinity/BarrattEccles/SimplexCuts/OrderedPrefixCard.lean` は、現行では `card_filter_lt_orderEmbOfFin` を持ち、AR-W1 段3の所有元表にも宣言があるため表から外した。357本と207本の差150本には外部 import があり、うち144本の追加は `Mathlib.Data.ZMod.Basic`。本体という呼称から root を除いて逆辺を数える場合は549本中470本、238本中178本になる。

所要は約20分。検証記録は Git 外の `~/serre-evidence/ic-w1/im-w1-0997952dc/`。段1はここの報告と表で停止する。

## IM-W1 段2　承認分の適用

適用の基準は依頼指定の `0f85ac6fe`。同じ Lean 入力に対する監査のハードリンク対応を含む `e9295c659` まで取り込んだ。ビルド開始前に通知し、bulk 鍵と共有の並列枠1を使った。

| 本体（Archive を除く） | 前 | 後 | 差 |
| --- | ---: | ---: | ---: |
| ファイル | 34,208 | 34,071 | −137 |
| 全行（空行・コメントを含む） | 3,034,413 | 3,030,169 | −4,244 |
| 直接 import 行（外部を含む） | 128,099 | 126,883 | −1,216 |

A は本体の `public meta import` を1,075行外し、`Util/DeprecatedAlias.lean` を削除。専用の直接 import の補充は0本。SimplicialCombinatorics 側の定義と回帰試験は保持した。B は承認済み124本、予約入口10本、局所設定だけの2本を削除。Spectra の2本・IC-2 の4本・残す案407本は削除0本。残す案のうち root、`EInfinity`、`Entrypoints/Derived`、`Checks/Morita/U16Checks` の4本には承認された import の追従だけを当てた。残存する本体の変更行はすべて import 行。

B の53箇所を付け替え、直接 import を48行（本体31、スクリプト17）入れた。6箇所は重複または空の入口のため置換行0、1箇所は2行。外部への付け替えは `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings` の2箇所（root と `scripts/audit/shared.lean`）で、旧 `IdealPowerTorsionBaseChange` の公開依存を維持するため。 `CompleteFaithfullyFlatDescent` は旧 `CompleteTwoCohomologyAnnihilator` 経由だった `DerivedPurity` と `ScalarConeAnnihilators` に直接接続した。二つの設定ファイルは削除前に旧入口と依存先を直接 import する環境を比較し、2オプションが `true false`、実在する `HasDerivedCategory.standard` の instance 優先度が `none` で一致した。

旧 Rectification パス116件を台帳の `direct_relocations` に登録。旧パスの不在と各正本の存在を個別に確認した。正式監査や検査のモジュール名、配置の設定も追従した。現行の本体・スクリプト・blueprint・監査 manifest に削除したモジュールを解決しようとする参照は0件。台帳の移動元キーと過去記録は由来として残る。静的な到達差は root などから切り離した、回帰試験用の SimplicialCombinatorics 側の旧別名モジュールだけだった。

全34,071モジュールを、root 外も含めて明示的に対象にした。Lake は38,846ジョブを終了コード0で完了（7,821.8秒、対象一覧を読む道具のコンパイルを含む全経過7,834.7秒）。

変更前の記録監査は調整役の `e9295c659` の結果を用いた。変更後の追跡・freshness を確認したビルド・採取・判定の4集合は34,071本で一致した。root の閉包は29,852本、root 外は4,219本。成果物欠落は0。全対象の鮮度を確認した上で、Lake の記録が等しい20,118本を再利用し、13,953本を採取し直した。採取・判定の全経過706.9秒、前後比較12.2秒。変更後の成果物に削除済みのモジュールを import する記録は0件。

宣言は359,531件から359,519件。減った12件はすべて削除した `Util/DeprecatedAlias` の構文・環境拡張と実装（3件の公開名、9件の private 補助）。残す所有元ごとに、private を含むカーネル名、新旧の構造指紋、種類、公理の集合を照合し、キーの追加・欠落・主張差・公理差はすべて0。残存ファイルの補助名差は0。G2 合格、未判定0・許可外の公理0・直接 sorry 4件・推移依存164件。sorry の所有元・カーネル名は直接・推移とも前後で同じ集合。

正式監査108本と主定理の sorry 閉包が合格。監査ごとの終了判定は変更前と同じで、キャッシュを使わず直列で実行した。正式監査と閉包の全経過は5,126.0秒（閉包186.9秒）。変更前の比較には、同じ入力・監査ソース・manifest の SU-W1 取り込み時の108本と閉包の記録を使った。付随するレイヤー検査の構文読取エラーと配置検査の旧 A 一覧不一致は、変更前後で診断が同じ。レイヤー検査の読取に依存する一括入口を避け、既存の実行器で正式監査を個別に走らせた。ファイル数上限の診断は0件、正式監査の環境再試行は0件。全体ビルド開始から監査終了まで約3時間48分。

ログ、監査ごとの成否、前後の差分、import 付け替え全行は Git 外の `~/serre-evidence/ic-w1/im-w1-stage2-0f85ac6fe/` に保存した。
