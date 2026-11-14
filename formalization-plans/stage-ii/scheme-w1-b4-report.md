# SC-W1：B4 完了報告

2026-11-14。**B4 完了**。main `ad523c511`（B3 `16d6b4547` 以降）を `math/scheme` に取り込み、対象ビルドと全対象の小さい監査が成功した。2g 全体の完成ではない。続いて 2g-1 の A07 内 I03 に戻る。

一覧：済み 7／全体 12（うち追加 3）。

## 完了時点の結果

- 取り込み前の枝：`63e611ecc`。main の取り込み：`b31ed2d0e`、第二親 `ad523c511`。衝突なし。
- 基準 `c5c4436c0` より後に自分の枝で追加・変更した本体の Lean **289 本**。下書きは除外。取り込み直前に git の差分の一覧と JSON の全件一致を再確認した。
- 全 289 本を取り込み前の原ソース全バイト・module・schema で照合して採取。採取器は同一版。公式の全体 rewrite は **保留 0、改名による差分 0 本／0 行**。参照 257,809 件、commands 2,298 件。通常 import の書き換えも 0。
- 改名とは別の、既定の上限で elaboration を通すための型共有・証明分割は三本。`28e73a366`（SquareData の局所設定）、`fdb5cadc6`（Rees の成分と自然性の分割）、`2e175c115`（Proj の Čech H の対象と比較の共有）。既存の比較の名前・数学的仮定は保持した。詳しい型と行数は以下の履歴にある。
- main から入った AlgebraicGeometry の引用属性等の **4 ファイル・35 行**を保持。差分 0 の旧プレビューを丸ごとコピーする操作も、取り込み後のソースに古い参照索引で rewrite する操作も行っていない。主対象 289 本のソースは取り込み前の検証済みのバイトから変化していない。
- 取り込み後の対象ビルド：`lake build SerrePositivity.AlgebraicGeometry`、**4,825 ジョブ成功**。三本の変更と、直接の importer を含む入口を検証した。プロジェクト全体の root ビルドは調整役の担当。
- 取り込み後の小さい監査：全対象 **289 モジュールの読み込みを確認し、生成宣言を含む 2,269 宣言、標準三公理のみ**。対象外の全プロジェクトの宣言は監査していない。終了コード 0。
- ビルド・採取・監査は共有の鍵 `--class impl --wait 3600`。同時の待ちは常に一つ。昼の採取は 280 秒以内の組に分け、通常ビルド・監査も一回 30 分以内。作業用の脚本と診断は worktree 内 `scheme-drafts/b4/` に保持した。

対象一覧は [files.json](scheme-w1-b4/files.json)、取り込み前の全体検証は [full-before-summary.json](scheme-w1-b4/full-before-summary.json)、取り込み後の結果とログ・監査ソースの SHA-256 は [after-merge-summary.json](scheme-w1-b4/after-merge-summary.json)。この報告を含む先端を B4 の取り込み点とする。

I03・I04 の既存 API の照合は [整射近似のメモ](scheme-w1-2g-integral-colimit-note.md)。共同全射性の未検証の Lean は `scheme-drafts/IntegralModelColimit.lean` にある。B4 完了後に検証してから本体に移す。2g-1 の主項目は 7／12 のままで、一般の細分と Noether 模型の構成を完了扱いにしない。

以下は取り込み前からの検証履歴で、「未完了」「未取り込み」は各時点での状態を表す。

## 対象と固定したソース

- worktree：`SerrePositivity-scheme`、枝：`math/scheme`。
- 検証済み数学の先端：`122ac972cd74c5d1d2a04ca623dab53f921c6c37`。
- 基準：`c5c4436c0`。観測した main：`efa846fe81f40ac663cff5af62f55b901763d676`（B3 `16d6b4547` を含む）。
- 対象は基準から枝で追加・変更した Lean 289 本。drafts を除き、全て AlgebraicGeometry 配下。提供された 284 本に、その後に検証済みの IntegralModel 系 5 本を加えた。全一覧は [files.json](scheme-w1-b4/files.json)。
- main の B4-README と citation-attributes.md §14 に従い、共有の `bulk_namespace.py` を使った。展開した `namespace-rewrite-map.json` は modules 5,337、namespaces 45、declarations 19。通常 import の module-map との照合は該当 0。
- 全 289 本の SHA-256 と採取前 HEAD を [collection-state.json](scheme-w1-b4/collection-state.json) に保存した。失敗後にも全バイトが不変であることを確認した。Lean の修正、資源上限の変更、採取器の変更は行っていない。

## 完了した採取とプレビュー

各 20 本の組 00〜08、合計 180 本で collect と rewrite が正常終了。各組の review.json は空、ソース差分は 0 本・0 行。参照が空のための結果ではなく、例として組 07 の一つの capture に refs 543、commands 7 がある。

共有鍵は `--class impl --wait 3600`。一つの worktree からの待ちは常に一つとし、各採取は `gtimeout --kill-after=3s 280` で区切った。組の間には鍵を解放した。

原ソース、表、索引、プレビュー、全ログは作業木内の `formalization-plans/stage-ii/scheme-drafts/b4/` に保持した。`index-00`〜`index-08` のみ完全な files.json を持つ。これらは main 取り込み前のソースに対するものであり、取り込み後のソースへ流用しない。

## 失敗の診断

組 09 は 6 本を採取した後、次で終了コード 1：

```text
SerrePositivity/AlgebraicGeometry/ProjectivePerfCechH0SquareData.lean:59:0:
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

失敗ファイルより後の 13 本を新しい出力先（09-tail）で切り分けたところ、10 本を採取した後、次で終了コード 1：

```text
SerrePositivity/AlgebraicGeometry/ProjectivePerfectAffineCechComparison.lean:30:4:
(deterministic) timeout at `«abstract nested proofs»`, maximum number of heartbeats (200000) has been reached
```

いずれも 280 秒の壁時計の時間切れではなく、採取器が実行する Lean 内部の heartbeat 上限による失敗。採取器は Lake の setup を使い、`Elab.async` を false にする実装である。この同期化が失敗の原因かどうかは未確定。通常の対象ビルド成功と同期採取の違いを、道具側で確認する必要がある。

完全なログは `collect-09.log` と `collect-09-tail.log` に保存した。エラーとログの SHA-256 も collection-state.json に記録した。部分索引 6 本・10 本は診断用に残しただけで、組の成功数にもプレビュー完了数にも含めない。組 10〜14 は未実行。

## 次の作業

採取器の失敗を解消した後、固定した取り込み前ソースで未完の採取を新しい出力先へ行い、全 289 本のプレビューを揃える。保留 0 と差分を確認してから main を取り込み、差分を適用する。その後、対象ビルドと小さい監査を通して B4 の完了を報告する。今回の 180 本の保留 0 を、全対象の保留 0 と読み替えない。

数学の直前の検証は 122ac972c に記録済み（AlgebraicGeometry の対象ビルド 4,824 ジョブ成功、新しい IntegralModel 系 5 本の小監査 26 宣言・標準三公理）。これは取り込み前の検証であり、B4 後の検証ではない。B4 が済んでから、2g-1 の A07 内の I03（実際の filtered colimit）へ戻る。

## 再開時の elaboration の整理（検証前の型つき一覧）

2026-11-14。共有の道具に更新がないため、自レーンの定義の elaboration を、型を変えずに整理して同期採取で検証する。資源上限は変えない。

- `projectivePerfCechH0Difference`：同じ定義一つについて `backward.isDefEq.respectTransparency true` を局所指定。同期採取で成功した。
- `projectivePerfectAffineCechOpen_isAffine (i)`：`IsAffineOpen (projectiveProjCechOpen G i)`。元の定義内の局所証明を外へ出す。
- `projectivePerfectAffineCechOpen_iSup hspan`：`(⨆ i, projectiveProjCechOpen G i) = ⊤`。同じ被覆性の局所証明を外へ出す。
- `projectivePerfectNativeCechHomologyIso (q)`：既存の `projectivePerfectNativeCechComplexIso` に homologyFunctor.mapIso を適用した同型。元の定義の前半を分割する。
- 既存の `projectivePerfectAffineCechHomologyIso` の型・名前を保ち、上の同型と同じ共通被覆比較を合成する。

上の補助宣言は既存の比較の法則と証明分割で、2g-1 の主項目には追加しない。証明分割を検証するまでは Lean をコミットしない。

一覧：済み 7／全体 12（うち追加 3）。

追加の証明分割：`projectivePerfectAffineDiagonal : IsAffineHom (pullback.diagonal (terminal.from (Proj G)))` を既存の instance から証明し、同じファイルの比較で局所 instance として共有する。型クラスの巨大な証明項を比較の定義へ繰り返し埋め込まないための分割であり、仮定を追加しない。

同じ比較の後半も `projectivePerfectCommonAffineCechHomologyIso hspan V hV hcV q` として分割する。型は標準開の Frobenius 係数の Čech H と V の同じ係数の Čech H の同型で、既存の共通被覆比較の適用そのもの。元の定義は前半と後半の合成を保つ。

## 再開時の検証結果：一つ解消、一つ未解消

`projectivePerfCechH0Difference` について、局所的に `backward.isDefEq.respectTransparency true` とする 1 行の変更だけを採用する。型・定義本体・名前に変更はない。同期 collect は既定の 200,000 heartbeats のまま成功し、その capture を使った rewrite は保留 0・差分 0。対象ビルド（SquareData と直接の importer SquareZero）は 3,379 ジョブ成功。この 2 モジュールの小さい監査は生成宣言を含む 48 宣言、標準三公理のみ。検証記録のハッシュは [verified-square-fix.json](scheme-w1-b4/verified-square-fix.json)。全体の採取・プレビュー確認済みは重複なしで 181／289 本になった。

`ProjectivePerfectAffineCechComparison` は未解消。局所的な透明性設定、アフィン性・被覆性の証明の分割、対角のアフィン性の共有、比較の前半・後半の分割、合成の中間対象の明示を、いずれも上限を増やさず試した。分割した宣言は通るが、最終的な `projectivePerfectAffineCechHomologyIso` の同期採取は `abstract nested proofs` で 200,000 heartbeats に達する。最後の中間対象の明示と局所設定の試行も同じ位置で失敗した。

試行した補助宣言は**全て本体から外した**。このファイルは元の 122ac972c のソースへ戻し、試行とログを `scheme-drafts/b4/` に保存した。既存の比較の型・定義的な振る舞いを、選択による別の構成へ置き換えることはしていない。共有の道具は変更していない。これから組 10〜14 の未実行部分を採取し、残る失敗の影響を切り分ける。main の取り込みは引き続き未実行。

一覧：済み 7／全体 12（うち追加 3）。

## 現在の到達点：287／289 本、残る同期採取エラーは二つ

組 11・12・13 の各 20 本、組 14 の 9 本、失敗した組の後ろに残っていた 7 本は正常終了した。単独で完了した組の採取・プレビューは計 257 本。途中で失敗した組の出力には、その失敗より前に `K.checked_capture` を経て保存された完全なファイル単位の capture が 30 本あった。

今回、この 30 本も含めて、標準の `checked_capture` で schema・module・原ソース全バイトの一致を改めて検査し、ファイル単位で重複を除いて別の `covered-before-index` に集約した。失敗した組全体を成功扱いにはしていない。失敗したファイルの capture は存在せず、集約にも含めていない。採取器の SHA-256 は全 287 本で一種類だった。

この明示的な **287 本の部分一覧**に対して公式の `bulk_namespace.py rewrite` を再実行し、全 287 本の保留 0・ソース差分 0 本／0 行を確認した。参照は 254,747 件、commands は 2,272 件。[確認済みの一覧](scheme-w1-b4/covered-files.json)、[不足の一覧](scheme-w1-b4/missing-files.json)、[集計とハッシュ](scheme-w1-b4/covered-summary.json)を保存した。これは全 289 本の検収の代わりではない。

残る失敗は次の二つ。

| 原ソース | 位置 | 同期採取のエラー |
| --- | --- | --- |
| ProjectivePerfectAffineCechComparison.lean | 30:4 | `abstract nested proofs`、200,000 heartbeats |
| ReesClosedCechThickeningFrobenius.lean | 29:4 | `abstract nested proofs`、200,000 heartbeats |

後者は組 10 で 14 本を正常に採取した後に失敗した。ログ `collect-10.log` を作業木に保持している。両方とも既存の対象ビルドが成功しているソースだが、同期採取の成功を示す証拠にはならないため、索引の網羅性の不足として明記する。前者に対する、型と意味を保つ複数の elaboration 整理の試行は上記のとおりで、全て下書きへ退避済み。採用した Lean の変更は SquareData の局所設定 1 行のみ（`28e73a366`）。

main の観測値は依然 `efa846fe8`。main の取り込み、取り込み後の新配置への差分適用、取り込み後の対象ビルド・小監査は**未実行**。取り込み前の索引・原ソース・プレビューを保持したまま、上記二つの同期 elaboration 失敗の確認が必要である。未検証のソース変更や、資源上限の引き上げで B4 を通したことにはしない。

B4 の全 289 本が揃い、main 取り込みと対象ビルド・小監査が済んでから 2g-1 の A07 内 I03 へ戻る。2g 全体は未完了で、目標・外枠・停止点を変更しない。

一覧：済み 7／全体 12（うち追加 3）。

## 再検証：Rees 側の既存の自然変換の証明分割（検証前）

2026-11-14。main 2be485f04 の追記は未変更の子名前空間の open の扱いであり、今回の同期 heartbeat 超過を解消する道具の変更はなかった。Rees 側も局所的な透明性設定だけでは同じ `abstract nested proofs` で失敗したため、その試行は戻す。

既存の自然変換を次の形で分割して検証する。新しい構成・主張や仮定を足さず、主項目の数は変えない。D を厚さ n・次数 d の既存の図式、E を厚さ p^e*n・次数 p^e*d の図式、φ を同じ反復 Frobenius と書く。

- `reesClosedChartThickeningFrobeniusApp (n e d T) : D.obj T ⟶ (E ⋙ ModuleCat.restrictScalars φ).obj T`：元の app フィールドを分離する。
- `reesClosedChartThickeningFrobeniusApp_naturality (h : T ⟶ U)`：`D.map h ≫ app U = app T ≫ (E ⋙ restrictScalars φ).map h`。元の自然性の証明をそのまま分離する。
- 既存の `reesClosedChartThickeningFrobeniusNatTrans` の型・名前を保ち、上の成分と証明で同じレコードを構成する。

一覧：済み 7／全体 12（うち追加 3）。

同じ比較の合成の別の分割案（検証前）：`projectivePerfectCechIsoTrans {X Y Z : ModuleCat.{u} ℤ} (a : X ≅ Y) (b : Y ≅ Z) : X ≅ Z := Iso.trans a b` を使い、既存の同型の合成を一つの名前で共有する。通常の Iso.trans と定義的に同じで、新しい比較や選択を導入しない。元の `projectivePerfectAffineCechHomologyIso` の型を保ち、同じ二つの同型をこの関数で合成して同期採取する。

## 再検証の成果：Rees 側を解消、288／289 本へ

Rees の成分と自然性の証明を分離し、レコードの暗黙引数を元と同じ指定に直した版で、既定の 200,000 heartbeats の同期 collect が成功した。単独の rewrite も保留 0・差分 0。成分と自然性の本文は字下げを除いて元と同一であることを照合した。

対象ビルド（ReesClosedCechThickeningFrobenius と直接の importer ReesClosedCechThickeningNaturality）は 3,058 ジョブ成功。この二モジュールの小監査は 17 宣言・標準三公理のみで、終了コード 0。記録は [verified-rees-split.json](scheme-w1-b4/verified-rees-split.json)。既存の型・名前は保持し、追加は元の app フィールドを分離した定義と、その自然性の証明だけ。

追加で試した、元の写像との rfl の比較例はカーネルの deterministic timeout になった。比較例とそのログを診断用に残し、成功とは数えない。公理監査はこの追加例から切り離して再実行し、終了コード 0 を確認した。新しい成分の本文と元の app の本文の直接照合、及び元の自然性の証明との直接照合はどちらも一致した。

確認済みは、前の 287 本とこの Rees の一つのプレビューを合わせて 288／289 本。前の covered-summary.json は 287 本のまま保存し、今回の一つの追加を上の検証記録で区別する。全体の再集約は残る Proj 側が揃ってから行う。

Proj 側の小さい合成関数の版（retry-affine-8）は、Rees の依存が stale であるため `lake --no-build setup-file` の段で終了した。この版を再び heartbeat 失敗したとは扱わない。Rees のビルドが済んだので、Proj 側の依存を含む対象ビルドを通してから、新しい出力先 retry-affine-9 で同期 collect をやり直す。未検証の Proj の変更はまだコミットしない。main は未取り込み。

一覧：済み 7／全体 12（うち追加 3）。

Proj の合成関数の版は対象ビルド 3,280 ジョブ成功後も、同期 collect では最後の定義の `abstract nested proofs` で 200,000 heartbeats に達した（retry-affine-9）。未検証のその補助関数を本体から外し、元の定義で Iso.trans の C・X・Y・Z をすべて明示する案を検証する。元の二つの同型、型、名前、資源上限は変えない。この案には新しい補助宣言はない。

Iso.trans の三対象を全て明示した版も、同じ定義の同期 `abstract nested proofs` で上限に達した（retry-affine-10）。続いて Mathlib `IsAffineOpen {X : Scheme} (U : X.Opens)` の X の推論を避け、元の定義の hV と hU で `X := Proj G` を明示した版を検証する。引数は元から Proj G の開集合で、仮定を強める変更ではない。補助宣言は増やさない。

IsAffineOpen の X の明示だけでも上限に達した（retry-affine-11）。次の証明分割では、既存の三つの対象を `projectivePerfectFixedCechH q`（固定した複体）、`projectivePerfectNativeCechH q`（同じ標準開の構造層）、`projectivePerfectCoverCechH V q`（比較先の有限被覆）として共有する。いずれも ModuleCat ℤ の既存の Čech H の対象の別名で、追加の数学的主張ではない。前に分割して検証した native の比較と共通被覆の比較の戻り型にもこの対象の別名を使い、公開する元の比較の型を保ったまま合成する。全て同じ構成の型と証明の分割で、主項目の数は変えない。

## 取り込み前の全対象の検証完了：289／289 本

三つの Čech H の対象を名前で共有し、前半・後半の比較の戻り型も同じ対象で共有した版で、最後の Proj の同期 collect が成功した（retry-affine-12）。公開する元の比較の型は保持する。追加は既存の対象と比較の型・証明の分割のみ。新しい数学的仮定や、選択で別の比較を作る構成は導入しない。

この Proj モジュールの通常ビルドは 3,280 ジョブ成功、小監査は生成宣言を含む 17 宣言・標準三公理のみ、終了コード 0。[検証記録](scheme-w1-b4/verified-affine-compact.json)。

全 289 本の完全な capture を、標準の schema・module・原ソース全バイト一致の検査で再集約した。採取器は全て同じ一版。不足 0。本来の全 289 本の一覧で公式 rewrite を再実行し、**保留 0、改名によるソース差分 0 本／0 行**を確認した。参照 257,809 件、commands 2,298 件。[全体の取り込み前集計](scheme-w1-b4/full-before-summary.json)。最初から対象の JSON に含まれていたファイルだけで、下書きは含めない。

改名とは別に、同期 elaboration を既定の上限で通すために変更した自レーンの Lean は三本。122ac972c との比較で、SquareData は +1/-0 行、ProjectivePerfectAffineCechComparison は +73/-10 行、ReesClosedCechThickeningFrobenius は +53/-34 行。型の共有、既存の証明の分割、局所の透明性設定であり、既存の名前・数学的仮定は保持した。三本の import は元と一致し、他の 286 本も全バイト一致のままなので、最初の通常 import の module-map 照合で該当 0 だったことも変わらない。

この検証済みの Proj の変更をコミットしてから main を取り込む。取り込み後のソースに古い索引で rewrite しない。全体のプレビュー差分が 0 なので、取り込み後に旧ソースを丸ごとコピーする操作も行わない。取り込み後の対象ビルドと小監査はまだ未実行で、B4 の最終完了はそこで報告する。

一覧：済み 7／全体 12（うち追加 3）。
