# 段階 II ⑤a 作業報告

## BS-DOC1 停止点 1（2026-11-07）

基準は開始時の main `b5c6cbff2`（`2c5d7e414` を含む）。専用 worktree は `../SerrePositivity-bs-impl`、枝は `math/bs-impl`。

### 原典と型の照合

[doc1-check.csv](../../../research/bs-coverage/doc1-check.csv) に `items.csv` の本体対応 184 行（論文 71 項目）を記録した。同じ宣言を別の論文項目に対応づけた行は別々に判定した。

| 判定 | 行数 | 扱い |
| --- | ---: | --- |
| `ok` | 149 | 宣言の主張または対応する部分を確認。特別な場合、証明中の対応箇所、E3 界面の欄などは範囲を明記 |
| `fix` | 34 | その番号での書き換え対象から外す。番号違い、補助結果、誤抽出、参照先の修正は理由欄に記載 |
| `unsure` | 1 | E3 の `perfd` 欄への Definition 8.2 の直付けを保留。型に原文の構成式や E∞ 構造が現れない |

- 184 行のうち 182 行の参照先をソース上で解決し、重複と表記ゆれをまとめた完全修飾名 162 個を `#check` した。残る 2 行は、10.1 の参照先が実際には別ファイルの `SerrePositivity.perfectoidIdeal` であるものと、16.3 の関連モジュールだけを挙げたもの。前者の実体と後者の `PrincipalDPPresentation` も追加の `#check` で型を得た。F-2 改名表の旧名に一致する対象宣言は 0 個。
- worktree を起点に一時ファイルで各対象モジュールを `import all` し、`pp.fullNames` を有効にして Lean 4.35.0-rc4 で型を取得した。main 側にある既存の `.olean` と依存パッケージの成果物を `LEAN_PATH` に読み取り専用で指定し、worktree のソースの型・定義も照合した。復元された成果物には個別のソースハッシュを持たない合成 trace がある。ここでの検証は既存環境での型確認で、新規のソースビルドは 0 回。
- 著者版 `paper/refs/BS-prisms-author.pdf` を参照した（SHA-256 `4cb49a42c80fc734fb7585da273538e09632431ba06709ae05a11ded6673c27a`）。Definition 1.4 は有界性であり、`DeltaStructure.IsPerfect` は Definition 2.26 に対応する。Proposition 7.2 の始 prism の存在と、構成中の δ 除算・ねじれ除去を分けた。16.9 は著者版では q-PD 対の Example で、表に載る半 perfectoid 商の全射性は Theorem 7.4 に対応する。
- E3 の欄は型を持つ構造体の射影として記録した。存在を引用する `exists_perfectoidizationInterfaceE3` は `Nonempty E3` を述べるため、Theorem 10.11 単体の対応から外した。8.5 は `limitCone` の範囲を指定錐のデータに限り、極限性を与える別の欄 `limit_isLimit` も型を確認した。

### 段 2 の件数見込み

- `ok` 149 行をまとめると **45 ファイル、136 宣言**。概要に番号を新規に入れる候補は **80 宣言**。残る **56 宣言**は既存 docstring に種別付き番号があり、表記・位置・範囲の整形を確認する。序論と本文が重なる場合は本文の番号を先に置く。保留 1 行はこの見込みに含めない。
- BS ディレクトリ内の **144 ファイル**すべてに先頭の module docstring がある。うち **68 ファイル**は先頭の module docstring に、著者版の項目として機械的に拾える種別付き番号がなく、節・項目との対応の追記候補。ファイル内のコメント全体でも同じ条件で拾えないものは **42 ファイル**。この抽出は種別付き番号で数えるため、元の指示書の 34 ファイルとは集計条件が異なる。
- `fix` の補助結果は、必要に応じて module docstring で論文との関係を述べる。個別の宣言にすでに別の `ok` 対応があれば、その番号の候補として扱う。

### 既存の引用表記

BS 144 ファイルと対応表に出る外部 7 ファイルの計 151 ファイルについて、Lean のコメント内の英語種別と二段番号を出現ごとに数えた。`Lemma 2.23〜2.25` などの後続番号を独立した出現として数えず、節番号も別扱い。module docstring の列は節見出し用の `/-!` も含む。出典名なしの一致は候補抽出であり、出典の確定は文脈で行う。

| 表記の形 | 宣言 docstring | Module docstring | 通常コメント | 計 |
| --- | ---: | ---: | ---: | ---: |
| `BS 著者版` ＋ 正式種別 | 19 | 27 | 0 | 46 |
| `BS 著者版` ＋ 略記 | 11 | 49 | 0 | 60 |
| `BS著者版` など空白違い ＋ 正式種別 | 5 | 13 | 0 | 18 |
| `BS著者版` など空白違い ＋ 略記 | 2 | 0 | 0 | 2 |
| `BS著者公開版` ＋ 正式種別 | 0 | 11 | 0 | 11 |
| `BS` ＋ 正式種別 | 63 | 11 | 0 | 74 |
| `BS` ＋ 略記 | 1624 | 311 | 0 | 1935 |
| `著者公開版` 等、BS 表記なし ＋ 正式種別 | 1 | 18 | 0 | 19 |
| `著者公開版` 等、BS 表記なし ＋ 略記 | 0 | 9 | 0 | 9 |
| `Bhatt–Scholze` 系 ＋ 正式種別 | 0 | 1 | 0 | 1 |
| `Bhatt–Scholze` 系 ＋ 略記 | 0 | 1 | 0 | 1 |
| 出典名なし、著者版と種類・番号が一致 ＋ 正式種別 | 26 | 72 | 0 | 98 |
| 出典名なし、著者版と種類・番号が一致 ＋ 略記 | 104 | 219 | 0 | 323 |
| 出典名なし、著者版と種類・番号が不一致 ＋ 正式種別 | 0 | 1 | 0 | 1 |
| 合計 | 1855 | 743 | 0 | 2598 |

`Perfectoidization/RootTower.lean` の出典名なしの `Theorem 2.5` は `Paper/Section2/LengthAlgebra/MixedChar` を指す。書き換え対象外。表の `BS 著者版` ＋ 正式種別 46 出現には概要以外の箇所も含む。

### 引き渡し

保存対象は確認 CSV とこの報告の 2 ファイル。⑤b の作業木・差分および進行中に入った main の変更とは、保存対象の重複なし。BS-DOC1 は停止点 1 で止め、段 2 の docstring 編集は調整役の承認後に進める。W11 の開始条件は BS-DOC1 の main 取り込み。

## BS-DOC1 停止点 2（2026-11-07）

main の `6dd825028` を `math/bs-impl` に取り込み、指示書 §4 の承認と追記を反映した。docstring の変更は `bcc42a7b8` と、行長を調整した `f22bf282a`。

- 本体 151 ファイル（BS 144、周辺 7）の引用表記を統一した。照合で採用した 136 宣言と追加承認された E3 の `perfd` 欄の計 137 件に、概要の末尾で範囲を付けて番号を記載した。E3 の `limitCone`、`excision`、`universal`、`integral` とあわせ、各欄が受け取る性質を説明した。
- 89 ファイルの先頭の module docstring に論文との関係を追記した。`fix` の補助結果と別の帰結はここで位置づけ、たとえば始 prism の Proposition 7.2 と、その証明に使う δ 除算・ねじれ除去を分けた。E3 全体の引用元も module docstring にまとめた。CLMST、HA、論文の層の混標数 Theorem 2.5 など、別文献の番号は元のまま。照合 CSV と `items.csv` は停止点 1 から変更なし。
- 差分検査では、ネストしたブロックコメントと行コメントを字句的に除外し、文字列・文字リテラルを保持した上で、コメント外の非空行を基準と比較した。151 ファイルで一致し、`git diff --check` も通った。main の既存成果物との比較では、151 本の公開 `.olean` と `.ir.sig` のハッシュが一致した。
- 段 2 のビルドは最大 16 対象ずつ。変更モジュール 151 本を 10 組、実行時間計 1587 秒で確認した。編集で新たに 100 字を超えた 32 行を整えた後、その 21 本を 2 組、計 204 秒で再検証した。実行前に `ps -axo command=` を確認し、毎回 `with_build_lock.sh --wait 0` を経由した。計測は他レーンの鍵待ちを除く。
- ⑤b の追跡差分と未追跡ファイルを照合し、変更パスの重複は 0。条件を満たしたので段 3 に進む。

## BS-DOC1 停止点 3（2026-11-07）

- 変更済みの 151 モジュールを直接 import する、変更対象外の 30 モジュールを 2 組、実行時間計 23 秒で確認した。Lake が既存成果物を再利用し、プロジェクトの Lean モジュールの再コンパイルは 0 本だった。ログには既存の警告が再表示された。対象には BS の集約、CLMST と Paper の直接 importer、共通基盤の直接 importer を含む。`ps` と共有ロックを経由した。ルート `SerrePositivity` も直接 importer だが、全体ビルドになるため調整役の合図待ちに分けた。
- 基準からの Lean 差分は 151 ファイルすべてコメントだけ。段 1 の照合 CSV と本報告が引き渡し資料。`items.csv` と drafts の変更はこの束に含まれない。⑤b の作業パスとの重複は 0。
- `math/bs-impl` は調整役の取り込み待ち。W11 の開始条件は BS-DOC1 の main 取り込み。

停止点 3 の後、⑥ の移動を含む main `4fbd8c0b7` を `eb30f187d` で取り込んだ。151 ファイルのコメント外差分は引き続き 0 で、⑤b の作業パスとの重複も 0。取り込み後に共有ロックで `SerrePositivity.BhattScholze` と `SerrePositivity.Paper.Section2.LengthAlgebra.MixedChar` を再確認し、成功した。

## BS-W11 停止点 A-1（2026-11-07）

基準は開始時 main `f40c91f43`（BS-DOC1 の取り込み `7032f9c59` を含む）。`math/bs-impl` の W11 最初のコミット `41f07e792` で、`RootTower/PerfectBaseChange.lean` の 25 行目を module docstring の改行だけで短くした。

- `drafts/A5/RootAdjunction.lean` の内容を独立した一時ファイルに写し、43 宣言（インスタンスを含む）を `lake env lean -DrelaxedAutoImplicit=false` で型検査した。1 ファイル、壁時計 10.08 秒、終了コード 0。現行の名前空間を使い、環の余極限の import を明示し、関係式の `p` の型注釈と `include` の位置を補った。定義の内容、引数順、定理の仮定と結論は下書きの意図どおり。F-2 の deprecated alias は使っていない。
- `algebraicRootClosure_filteredColimit` は通常の可換環の filtered 図式に対して `Limits.colimit.post D (algebraicRootFunctor p)` が同型という形。完備化を挟む `rootClosure` については、射の関手性までを扱う。
- 予定する import の到達先をソースから探索した（本体 461 モジュール）。`BhattScholze.Inputs.PerfectoidizationInterface` への経路は 0。環の完備化には `Perfectoidization.Derived.Interface` の既存 `completionRing` とその普遍性を使う。⑤b の差分とのパスの重複は 0。
- 未証明箇所は下書きから写した 17 か所。延長性・関手性・濃度、代数的根添加の filtered 余極限と mod p Frobenius、有限変数の根の関係・perfectoid 性・完全忠実平坦性が残る。A-2 では延長性と完備性から着手し、多変数環の perfectoid 性には完全 δ 環での根変数の Frobenius と完備化の比較を調べる。濃度と、閉じられなかった宣言は drafts に置く。
- 取り込み時の登録候補は `SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction`。この停止点の新規本体モジュールは 0 本。型が同じことを確認したため、A-2 の証明へ進む。

## BS-W11 停止点 A-2（2026-11-07）

実装コミットは `a611163b3`、`3a0a86f09`、`c65fdcd38`。作業 A の新規モジュールで、次を証明した。

- 完備な一段と可算塔からなる根添加を構成した。perfectoid 環への環射は一段ごとに延長でき、逐次余極限と完備化の普遍性で `rootClosure` を通る。完備性と、単位との両立・恒等射・合成を含む根添加の関手性も確認した。
- 完備化前の `algebraicRootFunctor` を構成した。mod p の任意の元は逐次余極限のある段から来るので、次段の関係式で p 乗根を取れる。
- 有限変数の多項式環と根添加環の間の射、根の関係式、評価による完備な底変換 `rootCover` を構成した。多項式商を非負の p 冪分母指数の単項式代数と同一視し、完全 δ 環上の単項式代数からの distinguished 主イデアル商で `polyRootAlgebra_isIntegralPerfectoid` を証明した。係数の p ねじれは有界 p ねじれとして完備化の比較に取り込み、下書きの仮定を保った。

### ビルドと依存

- 共有ロックで `SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction` の単体ビルドを 3 回実行し、順に 16 秒、16 秒、25 秒で成功した。最終の 25 秒のうち対象の再コンパイルは 18 秒。A の開始時には `PerfectBaseChange` と `SerrePositivity.BhattScholze` の 2 対象を同じロックでビルドし、13 秒で成功した。25 行目の行長警告は解消し、13 行目の既存の警告は残る。新規モジュールには未使用のセクション引数と tactic の書き方に関する警告がある。
- 本体への追加は sorry・admit・独自公理が各 0。公開宣言 45 件（環代数のインスタンス 5 件を含む）の `#print axioms` は標準の `propext`、`Classical.choice`、`Quot.sound` の範囲内。新規モジュールを含む本体 631 モジュールの import をたどり、`BhattScholze.Inputs.PerfectoidizationInterface` に到達する経路は 0。
- 本体の変更は新規 1 ファイルと `41f07e792` の docstring 改行のみ。既存の宣言は変更なし。ほかの差分は A5 の下書きとこの報告。⑤b の `5958651b6` と作業木、および基準から進んだ main `5c2fa9423` に対象パスの重複は 0。差分の空白検査も通った。

### drafts に残る宣言

| 宣言 | 残る証明 |
| --- | --- |
| `rootClosure_cardinal_le` | 各段の濃度評価と、可算余極限・完備化を通した上界。 |
| `algebraicRootClosure_filteredColimit` | 一段が filtered 余極限を保つことと、逐次余極限との交換。 |
| `polyAlgebraToRoot_pCompletelyFaithfullyFlat` | 通常の多項式環上の分数指数基底と、完備化後の忠実平坦性。 |

### 取り込み時の登録

- 新規登録モジュールは `SerrePositivity.BhattScholze.Perfectoidization.Derived.RootAdjunction` の 1 本。共通入口 `SerrePositivity/BhattScholze.lean` と BS 監査スクリプトへの登録、および登録後の単独監査は調整役が行う。A-2 で検収を待つ。

## BS-W11 停止点 B-1（2026-11-07）

A-2 取り込みと監査の登録を含む main `2d79d1de2` まで `math/bs-impl` を fast-forward した。

- `drafts/A6/ArcSite.lean` の G-A6-11・G-A6-3 と、`ArcSheafProperty.lean` の 1c・G-A6-6 を一時ファイルに写し、`lake env lean -DrelaxedAutoImplicit=false` で型検査した。28 宣言（構造体とインスタンスを含む）、壁時計 10.12 秒、終了コード 0。対象の仮定、結論、根添加の表示、Milnor 列の脚を下書きと揃えた。完備化・体拡大の 2 宣言には下書きどおり重複する素数性のインスタンスがあり、型検査では警告が出る。
- tilt の二つの定理が参照する `tiltRing` と `tiltRingEquivPreTilt` も同じ下書きにあるので、比較のため同じ型で定義した。原典の逆極限に沿い、mod p が零環なら零環、そうでなければ `PreTilt`。対象の p 完備環では、この分岐は下書きの零環の場合分けに一致する。
- 一時ファイルに未証明箇所 14 件。B-2 の根の塔、テンソルと延長、Milnor 短完全列から進め、B-3 では付値環の拡大と tilt・untilt を扱う。W12 から使う 1c は任意の付値環と素イデアルを取る形を維持する。忠実平坦な拡大は p 完備かつ階数 1 のまま扱う。
- 一時ファイルの import から本体 470 モジュールをたどり、E3 への経路は 0。⑤b の差分・作業パスと予定する対象の重複は 0。新規本体モジュールはこの停止点では 0 本。移行先は A6 の配置規則に従い `BhattScholze/Perfectoidization/Derived/`。型が揃ったので証明に進む。

## BS-W11 停止点 B-2（2026-11-07）

実装は `0367d6bc4` と `d73baf34b`。両モジュールとも既存の宣言を変更せず、drafts から証明済みの宣言を移した。

- G-A6-11 の `perfectoidBaseRing_isPerfectoid` を証明した。下書きの多項式商を一変数の根の塔の直極限と同定し、係数の mod p を `ZMod p` と比較して既存の完備塔の定理を適用した。p の正則性で古典的完備化から導来 H⁰ の表示へ移した。
- 導来 p 完備な離散環への標準 ℤ_p 射とその一意性を、整数の完備化の各剰余環を通して示した。`baseExtension` とその導来完備性、`perfectoidBaseRing_toValuationExtension` と `exists_baseExtension_lift_of_map` を実装した。両脚の ℤ_p 上の一致により、与えられた拡大に沿って底変換を延長する。
- 1c の `valuationRing_milnorSquare` と完全付値環への特殊化を証明した。任意の素イデアルで局所化し、剰余が零となる分数は分母で割り切れるので元の素イデアルから来ることを使った。B-1 の加法群の短完全列の型を保った。

### ビルドと依存

- 共有ロックで Milnor の単体ビルドは 6 秒、既存の `RootTower.Perfectoid` の成果物復元は 4 秒。R₀ と底変換の単体ビルドは初回 17 秒、行長調整後 11 秒で成功した。Milnor の完全環への特殊化には、下書きと同じ素数性引数に関する未使用引数警告が残る。
- 調整役の段階 II 監査を一時ファイルに写し、新規 2 モジュールを対象として共有ロックで単独実行した。生成宣言を含む 99 件が標準三公理のみ。sorry・admit・独自公理は 0。新規モジュールを含む本体 587 モジュールの import を確認し、E3 に到達する経路は 0。
- ⑤b の `2846f2a1a` と作業木、および基準から進んだ main `cf3f9e3b7` と変更パスの重複は 0。差分の空白検査を通過した。

### drafts に残した主張

- `baseExtension_cardinal_le` はテンソルの有限和と導来完備化の可算データの濃度評価が残る。
- `baseExtensionUnit_pCompletelyFaithfullyFlat` は一般の導来 p 完備な S について、完備底変換と Tor・忠実性の比較が残る。
- `exists_baseExtension_lift` は同じ W を先に選ぶ G-A6-3 を使うため、B-3 の付値環の拡大の後に扱う。tilt・untilt も B-3。

### 取り込み時の登録

- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcPerfectoidBase`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationMilnor`

共通入口と `scripts/audit_bhatt_scholze_stage2.lean` の登録は調整役が行う。対象のビルドと単独監査が通ったので B-3 に進む。

## BS-W11 停止点 B-3（2026-11-07）

実装は `721574dcc` と `9ffa38a4e`。間の `056a487c2` で、B-2 の登録 `978cc71ea` と指示書 §8 を含む main `f48441f89` を `math/bs-impl` に取り込んだ。

- G-A6-3 の `exists_perfectoid_valuation_extension` を証明した。分数体の代数閉包の付値部分環へ局所的に延長する。非零素イデアルの縮約は非零で、剰余への代数関係式は係数の一つを 1 に正規化して得られるため、拡大は階数 1。標数 p ではそのまま、混標数では p 進完備化して、Frobenius の全射性と p の両立根から perfectoid 性を示した。両方で忠実平坦性を証明し、同じ拡大を使って `exists_baseExtension_lift` を閉じた。
- `rankOneValuation_completion` は任意の階数 1 の付値環と任意の非零非単元に適用できる。完備化の元を元の付値環の元の単元倍で表し、階数と忠実平坦性を示した。完全な標数 p の場合は剰余環の逆 Frobenius で完全性を保つので、`arcValuation_completeAt` が従う。`arcValuation_extendField` は一変数の冪級数付値環を経由して G-A6-3 を適用した。下書きの主張の型は同じ。
- G-A6-6 の `tilt_rankOneValuationRing` と `untilt_rankOneValuationRing` を証明した。tilt では sharp の両立根の各成分で割って可除性を比較した。untilt では distinguished Witt 商の元を sharp の単元倍に書き、第零係数が零なら Witt 商を元の環と同定した。標準の tilt 写像との同型も得た。untilt の付値環性の計算は [Česnavičius–Scholze, Proposition 2.1.9](https://www.math.u-psud.fr/~cesnavicius/flat-purity.pdf) に沿う。

### ビルドと監査

- 共有ロックで `ArcValuationCompletion`・`ArcValuationTilt` の 2 対象を 10 秒、行長調整後に 9 秒でビルドした。`ArcValuationExtension`・`ArcValuationUntilt` の 2 対象は 18 秒で成功。下書きの型を維持した 2 宣言に素数性インスタンスの重複警告があり、未使用のセクション引数の警告もある。
- 段階 II 監査を一時ファイルに写し、共有ロック下で B-3 の新規 4 モジュールに対して単独実行した。生成宣言を含む 93 件が標準三公理のみ。sorry・admit・独自公理は 0。新規モジュールを含む本体 591 モジュールの import をたどり、E3 への経路は 0。
- 本体の作業差分は新規 4 モジュール。既存の本体宣言の変更は 0。⑤b の差分・作業木および取り込み後の main の変更との対象パスの重複は 0。差分の空白検査を通過した。

### 残る下書きと D の順序

B-3 の対象宣言はすべて本体へ移した。§8 に従い、`rootClosure_cardinal_le` と `baseExtension_cardinal_le` は D の最初に閉じてから Lemma 8.8 へ進む。`baseExtensionUnit_pCompletelyFaithfullyFlat` が Lemma 8.8 の証明に必要かは D-1 で確認する。

### 取り込み時の登録

- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationCompletion`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationTilt`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationExtension`
- `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcValuationUntilt`

共通入口と `scripts/audit_bhatt_scholze_stage2.lean` の登録は調整役が行う。

## BS-W11 停止点 C-1（2026-11-07）

B-3 の登録を含む main `3113117cd` へ `math/bs-impl` を fast-forward した。

- `drafts/A8/IntegralDiscreteness.lean` から G-A8-6 の宣言 1 件を一時ファイルに写し、`lake env lean -DrelaxedAutoImplicit=false` で型検査した。16.77 秒、終了コード 0。任意の整 perfectoid 環とその有限エタール代数を取る下書きの型を維持する。p の正則性や局所性の仮定は加えない。
- 相対 Frobenius の比較と平坦性を用い、Fontaine 核の生成元を移す方針。標数 p、混標数、p ねじれのある基底を含めて扱う。Mathlib の既存の有限エタール API と、リポジトリの Fontaine 核・tilt の補題を使う。
- この停止点の新規本体モジュールは 0 本。作業 C の対象パスと⑤b の差分・作業木に重複は 0。型が同じなので C-2 に進む。

## BS-W11 停止点 C-2（2026-11-07）

- G-A8-6 `isIntegralPerfectoid_of_finiteEtale` を `drafts/A8/IntegralDiscreteness.lean` から移し、下書きの型と引数順で証明した。零環・標数 p・混標数・p ねじれの場合を含む。同じ下書きの後続の宣言は残した。
- mod p で相対 Frobenius の全単射性を示す（[Stacks Project, Tag 0EBS](https://stacks.math.columbia.edu/tag/0EBS) に対応する半完全環上の形）。有限個の生成元の両立する p 乗根を選び、剰余 Frobenius の核から tilt の第 0 射影の核を移す。有限射影性で p 進完備性と p ねじれの持ち上げを得て、既存の distinguished Witt 商の完備性から Fontaine 核を計算する。
- 対象 1 モジュールのロック付きビルドは 12 秒（対象コンパイル 8.5 秒）。対象モジュール自身の警告は 0。単独監査は 25 宣言、標準三公理のみ。本体の sorry・追加公理は 0。推移的なローカル import は 73 モジュールで E3 入口へ到達しない。`git diff --check` を通過し、対象パスの⑤b との重複は 0。
- B-3 の未使用セクション引数は、一時ファイルで名前を付けて `include` しても警告が残った。警告対象の引数を `omit` すると型から外れるので、`completionInverseFrobenius_pow` と `arcValuation_extendField` の型を維持した。素数性インスタンスの重複もそのまま。
- 入口と段階 II 監査への登録は 1 本。 `SerrePositivity.BhattScholze.Perfectoidization.Derived.FiniteEtalePerfectoid`。

## BS-W11 停止点 D-1（2026-11-07）

- §8 の前段として `rootClosure_cardinal_le` と `baseExtension_cardinal_le` を下書きと同じ型で証明した。導来完備化の H⁰ は既存の可算列の商表示を使う。根添加では各段の多項式環と可算余極限、底変換では ℤₚ の有理 Cauchy 列表示とテンソルの有限和表示を評価した。
- `ArcCardinality` の対象ビルドは 9 秒（対象コンパイル 3.8 秒）。対象自身の警告は 0。単独監査は 11 宣言、標準三公理のみ。本体の sorry・追加公理は 0。推移的なローカル import は 647 モジュールで E3 入口へ到達しない。
- `AffCompl`・`AffPerfd`、有限 arc 被覆族と位相、coverage の底変換・合成・有限積、`exists_perfectoid_arcCover`・`affPerfdInclusion_isCoverDense` を下書きの型のまま一時ファイルで検査した。12.22 秒、終了コード 0。未証明 6 件は型検査用の一時ファイルに置いた。
- Lemma 8.8 の affine 版で必要な忠実平坦性は、各試験付値環の拡大 `V → W`。既存の `exists_baseExtension_lift` で、同じ `W` への `S₀ → W` と元の `S → V` との両立が得られる。この射を根添加と普遍 perfectoid 化に沿って延長するので、一般の `baseExtensionUnit_pCompletelyFaithfullyFlat` は drafts に残す。
- D-2 の証明に進む。半 perfectoid 商を与える箇所は、標数 p の剰余 Frobenius と、整 perfectoid 基底から来る distinguished 元を用いる。∞ 圏の Čech 比較は別工程。⑤b との対象パスの重複は 0。`git diff --check` を通過した。
- 入口と段階 II 監査への追加候補は 1 本。 `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCardinality`（D-2 取り込み時）。

## BS-W11 停止点 D-2（2026-11-07）

- `ArcSite` に、`AffCompl`・`AffPerfd`、有限 arc 被覆族、生成される位相と誘導位相、底変換・合成・有限積の比較、`exists_perfectoid_arcCover` と `affPerfdInclusion_isCoverDense` を移した。完備性の仮定は下書きどおり。底変換の証明で使わない三引数には、型を保って名前の先頭に `_` を付けた。
- Lemma 8.8 の affine 版では、導来根添加の mod p Frobenius の全射性を示し、古典的 p 完備化に移した。基底の Fontaine 核の distinguished 元を使って完全 prism の商からの全射を得て、既存の全射な普遍 perfectoid 化を適用した。対象の濃度には D-1 の両方の評価を使う。持ち上げの忠実平坦性は試験付値環 `V → W` のもの。
- `ArcSite` の対象ビルドは 19 秒（対象コンパイル 12 秒）。対象自身の警告は 0。`ArcCardinality` と `ArcSite` の単独監査は 37 宣言、標準三公理のみ。本体の sorry・追加公理は 0。推移的なローカル import は 679 モジュールで E3 入口へ到達しない。⑤b との対象パスの重複は 0。`git diff --check` を通過した。
- 残る下書きは、A5 根添加の filtered 余極限との可換性と完備忠実平坦性（2 件）、A6 の相対 Čech 比較と生成系からの層条件、および一般の `baseExtensionUnit_pCompletelyFaithfullyFlat`（計 12 件）。A6 の後者はこの被覆の証明で使わない。A8 の G-A8-6 より後の項目は引き続き drafts にある（20 件）。
- 入口と段階 II 監査への登録は、D-1・D-2 の計 2 本。 `SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcCardinality`、`SerrePositivity.BhattScholze.Perfectoidization.Derived.ArcSite`。C-2 の登録は C-2 の欄を参照。

### B-3 の警告整理

- `completionInverseFrobenius_pow` と `arcValuation_extendField` では、従来セクションから入っていた引数を同じ順序で明示し、未使用セクション引数の警告を解消した。変更前後の型は `#check @...` で照合した。素数性インスタンスの重複は従来の型に含まれるため残した。
- `ArcValuationCompletion`・`ArcValuationExtension`・`ArcSite` の再ビルドは 25 秒。前二者の単独監査は 41 宣言、標準三公理のみ。追加の登録は 0 本。
