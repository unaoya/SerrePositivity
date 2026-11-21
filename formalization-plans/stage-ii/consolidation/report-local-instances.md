# LI-W1 段1　局所 instance の分類と試し

**現在地**　段1は2026-11-21のユーザー決定で区切った。分類・対象ビルドは終了、型の前後照合は途中。基準は main `3ed0c1724`、調査と試しの枝は `refactor/local-instances`。分類・試行の結果をここに記録する。

## 1. 母集団と根拠

旧表と同じ抽出を現行ソースに適用した。局所宣言は **3,209件、1,705ファイル、714種**。旧表の3,210件からは、SU-W1 段13（`73ae4f10e`）で削除された `enrichedModelOrdinaryCategory` の1件だけ減った。反復で右辺の表記が一種の群は288種、複数の群は57種、一度の群は369種。局所属性は **1,604件、166種**で旧表と一致する。AR-W1 段10の A1 (i) は5種を追加した。[分類表](../../../research/cleanup-zero-base/local-instances/classification.csv) に計885行を収める。

ソースのコマンドと記録監査の型・本体・登録を、所有モジュール、カーネル名、宣言の位置で結び付けた。ドキュメントコメントが付く場合は宣言範囲の開始行と名前の位置が異なるため、両方を使った。局所宣言3,209件はすべて対応した。型の頭が同じ登録と、型・右辺の照合で同じ対象だと確認できる登録を区別した。Lean・Mathlib と依存パッケージの11,911モジュールの保存データも照合した。大域・scoped の優先度、元の定義、右辺のカーネル参照を根拠にした。同じ種類の構造に見えても、対象・宇宙・作用やモデルの引数を確かめ、登録先を決めた。

走査型のキーは旧表との比較のため保持した。Rees 群での `(ι := ι)` などに、文字走査が宣言の区切りとして扱った `:=` が含まれる。表のカーネル名と右辺の照合欄で、実際の完全な宣言を区別できる。同一型の確認には、カーネルの型を使った。

## 2. 分類と右辺の照合

| 分類 | 局所宣言の種類 | 局所宣言の件数 | 局所属性の種類 | 局所属性の件数 | A1 (i) の種類 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 1 大域 | 20 | 942 | 2 | 50 | 0 |
| 2 scoped | 176 | 1,300 | 29 | 496 | 4 |
| 3 Mathlib の作法 | 6 | 107 | 11 | 848 | 1 |
| 一度なのでそのまま | 369 | 369 | 88 | 88 | 0 |
| 判断できない | 143 | 491 | 36 | 122 | 0 |

大域登録候補は元の局所宣言 942件・2,218行、scoped 候補は 1,300件・3,315行。概算では大域登録1行を種類ごとに足して約 2,198行減、scoped の利用側を一件一行、登録側を一種一行として約 1,839行減。新たな提供宣言や import、既存の scope の再利用がある箇所で実数は変わる。明示名を参照する箇所には別途見直しが要る。局所属性、導来圏、単発と未確定の群はこの見積もりから外した。

AR-W1 の A1 (i) は、心を表す Mathlib の明示選択を規則3に入れ、残りの4種を規則2に入れた。心は `t.hasHeartFullSubcategory` が実際の値を供給する。残りはテンソル単位の置換、モデルと生成族、引戻しの選択、モノイドモデル構造に依存するので個別の供給元を表に示した。

Mathlib の具体例では、`CategoryTheory.uliftCategory` が半順序由来の圏との diamond を避けるため局所指定され、`MvPolynomial.algebraMvPolynomial` が二重多項式環の代数構造との diamond を避けるため局所指定される。一方、`adicQuotientAlgebra` は大域登録済みの `Ideal.Quotient.algebraQuotientMapQuotient` をそのまま返す。この差を規則3と規則1の判定に反映した。

右辺の表記が複数の57種・763件について、各群の完全な型と本体を調べた。ハッシュでまとまるものは代表を選び、別の表記・本体の代表と型が違って見える代表を Lean の `Meta.isDefEq` で比較した。355組の内訳は次のとおり。

| 比較結果 | 組数 |
| --- | ---: |
| 完全な型が定義的に等しく、同じ命題の証明 | 131 |
| 完全な型とデータが定義的に等しい | 45 |
| 完全な型が一致しない | 176 |
| 宇宙パラメータ数が異なる | 3 |
| 同じ完全な型で定義的に異なるデータ | 0 |

同じ型で異なるデータの組は0件だった。型が一致しない組には、対象・構造・束縛引数が違うものが含まれる。たとえば Kan 性の同一走査型には Ω スペクトルと反対圏の使い方が混ざり、Rees の群には同じ記法の引数を別の作用で解釈する例がある。束縛子や宇宙が異なる組には元の完全な型での比較結果を記録した。

## 3. 登録を変える試し

旧表と現行表の上位50の和集合は51種。旧47位の一般対称スペクトルの豊穣が現行57位になり、現行50位の Rees の全体加群のスカラー塔が加わった。提供元と、分野をまたいで選んだ利用側の最大13本（Ω スペクトルは14本）を、同じ Lean オプションで前後とも再コンパイルした。件数が少ない型や、対象にできる局所宣言が少ない型では選べる全ファイルを採った。既存登録を使う試行では、利用側の局所宣言の除去または標準名への追従を試した。

作業木のキャッシュを参照する一時コピーを用い、対象ビルドには `impl` 鍵を使った。全宣言の記録採取と型の前後照合は `bulk` 鍵で一度に一プロセス。型は同名の宣言を比較し、式に残る局所 instance の参照が変わったときは、元の定義を展開して同じ型か Lean でも調べた。時間は成功した同じファイルの前後で比べた。実測時間には他の作業の負荷も含まれる。増加した例は再測定の候補にした。

試行の内訳は分類表の「試し」に記録した。現時点で 51/51種、利用側 569本成功、28本失敗。提供元で停止した群 0種、import の循環で試案を除いた利用側 4本。

- Ω スペクトルの単体的豊穣化は提供元と利用側14本が通り、表現が変わった型32件はすべて定義的に一致した。
- 写像空間の Kan 性は、既存の `mappingSpace_kanComplex` への推論だけに任せる先行試行で13本中7本が失敗した。`SpectrumTailEquivalence` では `∀ X Y, (SimplicialCategory.sHom X Y).KanComplex` の合成に失敗し、`CanonicalFixedSourceFiber` では後続の `whnf` も heartbeat 上限に達した。選んだ Ω 豊穣を明示した scoped instance を提供元に置く再試行では13本すべて通った。
- QCat の Hom 圏は Mathlib の `Bicategory.homCategory` の既存登録を使うと、局所宣言を外した代表13本が通った。
- Barratt–Eccles のモデルは既存の `modelCategory` を scoped 登録した提供元と利用側13本が通った。選んだ模型に対する関手的分解も、専用の scoped instance で提供元と利用側13本が通った。
- 複体の余極限は既存の shape 用 instance だけに任せると、指定した宇宙の余極限を合成できない利用側があった。余積の `BarWeightEvaluationIso` は3.9秒から15.2秒になり、型クラス探索が20,000 heartbeatsで停止した。単独の `#synth HasCoproducts.{0} (Complex A)` でも、離散形の余極限から `instHasCoproductsOfShapeOfHasCountableCoproductsOfCountable` が可算余積を要求し、`hasCountableCoproducts_of_hasCoproducts` を通って同じ余積の目標に戻る経路をトレースで確認した。
- 整数次数の Rees 加群では `projectiveNatGradingIntSMul` の大域登録後も、`ReesIntegerCechComparison`、`ReesIntegerCechInclusion`、`ReesIntegerCechAction` で基礎環に制限した型の `GradedSMul` の合成に失敗した。元の局所宣言は `projectiveNatGradingInt_restrictScalars` による移送を含む。この移送を残す箇所を、提供元をそのまま呼ぶ箇所から区別する。
- 多項式の係数変更では、登録を試した `ProjectiveCoefficientChartTransport` が `ProjectivePolynomialCoefficientMapNaturality` を import し、後者は `ProjectivePolynomialCoefficientChange` を import する。下流の提供元をこの2本から import する案は循環するため、代数構造とスカラー塔の試行で計4件を除いた。`ProjectiveTensorPolynomialModule` では scope を開いても、代数構造を置き換えた際に必要な `SMul` の合成に失敗した。
- strict 図式の離散 shape の余積で局所宣言を外した `StrictDiagramFreeValueFrame` は、`∀ a b, HasColimitsOfShape (Discrete (a ⟶ b)) (Complex A)` の型クラス探索が20,000 heartbeatsで停止した。既存登録で通った12本との違いは、表に残した。
- `Fin 2 × Fin 2` で従来の局所登録を外すと、12本中11本が失敗した。`D3DoubleEndpointPullbacks` と `D3JointUnitStageComparison` の診断では、探索が `uniformProd (Fin 2) (Fin 2)` を選び、型が指定した `Preorder.smallCategory (Fin 2 × Fin 2)` と定義的に一致しなかった。この違いは反対圏からの関手の型にも現れた。分類は規則2とし、順序による圏構造を選ぶ scope を試した。
- Rees の全体加群に `reesAdicTotalBaseModule` だけを登録し、基礎環の `SMul` を外した試行は9本すべて失敗した。`ReesAdicGradedLocalizedDirectSum` では `IsScalarTower.of_compHom` が要求する合成の作用と、探索で得た部分加群の作用が型の上で食い違った。元の `reesAdicTotalBaseModule.toSMul` を明示する scope を別に試した。
- `ReesIntegerCechAction` で移送の宣言を残し、提供元を直接呼んでいた宣言だけを外す再試行は通った。
- `ReesIntegerCechComparison` で移送の宣言を残し、提供元を直接呼んでいた宣言だけを外す再試行は通った。
- `ReesIntegerCechInclusion` で移送の宣言を残し、提供元を直接呼んでいた宣言だけを外す再試行は通った。

`Too many open files in system` が記録された実行は 0 件。該当実行は Lean の成功・失敗から外した。

同名の型に相違があったもののうち、生成名の形に当たるものは69件、それ以外は0件。生成証明の連番が同じでも、前後で対応する証明部分がずれる場合がある。

生成名の相違が出た試行番号と件数。

- 06。型の相違 35、宇宙引数の数の相違 4、その他 0。
- 09。型の相違 7、宇宙引数の数の相違 0、その他 0。
- 14。型の相違 1、宇宙引数の数の相違 0、その他 0。
- 17。型の相違 11、宇宙引数の数の相違 2、その他 0。
- 30。型の相違 9、宇宙引数の数の相違 0、その他 0。

11-21 のユーザー決定で型照合を中断した。対象ビルドは51種すべて終了した。型の指紋に差の候補がある306モジュールのうち、照合を終えたのは236モジュール、未完了・再照合待ちは70モジュール。名前単位では未照合207件、照合器のエラー86件。照合器エラーでは追加 import 先の定数を読めていなかった。修正した照合器での再実行は中断時点で済んでいない。相違の記録は照合済みの範囲に限る。

## 4. 導来圏

Mathlib の `Algebra/Homology/DerivedCategory/Basic.lean` の *Implementation notes* は、主張が導来圏を含む場合に `[HasDerivedCategory.{w} C]` を仮定し、含まない主張の証明にだけ `HasDerivedCategory.standard` を導入するよう定める。標準局所化の射の宇宙は `max u v`。より小さい宇宙を選べる場合もある。

| 局所属性の有効範囲で確認できたこと | 件数 |
| --- | ---: |
| 主張の型またはソースに残る `example` の型に導来圏が現れる | 569 |
| 型に現れず、本体・証明のために標準の選択を使う | 51 |
| 記録から用途を確定できず、除去後もビルドが通る | 54 |
| 宣言も `example` もない範囲 | 1 |
| 計 | 675 |

範囲内で両方を確認した57件は「主張」に数えた。名前の付いた型の該当は重複を除いて2,017宣言。証明・本体の該当は、型に該当する名前を除いて143宣言。型の直接参照と型を返す project 定義、標準 instance の本体参照を照合し、環境に保存されない `example` はソースの型も読んだ。この照合で用途を確定できなかった56件を追加試行した。`EInfinity/Interface/Core.lean` の `EInfinityCore.discrete_recognition` は、型の `derivedInfinityHomology` に標準の選択を要した。`EInfinity/BarrattEccles/Theory.lean` の `barrattEcclesCore` は、構造体の本体で `discrete_recognition` を組み立てる際に選択を要した。表はこの2件を反映した。

主張を `[HasDerivedCategory.{w} C]` に一般化すると、導来圏と射の宇宙が呼び出し側から与えられる。選択が入っていた関手・シフト・三角圏構造がその選択で型づけられ、標準模型を使う呼び出し側では必要な所で `standard` を供給する。これは主張の型と公開インターフェースに及ぶ変更なので、登録変更とは別の取り込み単位になる。

用途を確定できなかった属性の除去を試した。46ファイル（54箇所）が通り、2ファイル（2箇所）が失敗した。除去後のビルド成功は、そのファイルを再検査した条件で属性を省けるという証拠になる。元の証明探索での利用は、上の集計区分のまま扱う。

成功した46ファイルでは、前後で宣言名・宣言種別・型と宇宙引数の指紋が一致した。

- `SerrePositivity/EInfinity/BarrattEccles/Theory.lean` の 32 行。error(lean.synthInstanceFailed): failed to synthesize instance of type class
- `SerrePositivity/EInfinity/Interface/Core.lean` の 34 行。error(lean.synthInstanceFailed): failed to synthesize instance of type class

## 5. その場で構造を作る箇所

`where` を持つ12件を以下に挙げる。右辺が空白正規化後160字を超えるか、空でない行が6行以上の249件は、分類表の「長い右辺の位置」にすべて記録した。長さは抽出の基準であり、その場で新しい構造を作るかは定義と証明を見て決める。

| 場所（`SerrePositivity/` 以下） | 一般化の候補 |
| --- | --- |
| `AlgebraicGeometry/ProjectiveCechTensorBaseChange.lean:24` | 係数拡張の加法性を `ModuleCat.extendScalars` の一般結果に寄せる。 |
| `AlgebraicGeometry/TensorExtendScalarsEquiv.lean:21` | 係数制限した環上のスカラー塔として取り出す。 |
| `EInfinity/PowerOperation/CyclicTensorUnitComparison.lean:24` | 自明表現の関手の加法性を作用を忘れる関手の側に置く。 |
| `HomologicalAlgebra/AlgebraKoszulColimit.lean:141` | 係数制限の完全性から whiskering のホモロジー保存を得る。次の局所コホモロジーの箇所と共用候補。 |
| `HomologicalAlgebra/Cosimplicial/CohomologyCupGradedRing.lean:133` | cup 積の次数0の単位を graded ring の提供元に寄せる。 |
| `HomologicalAlgebra/Cosimplicial/CohomologyCupGradedRing.lean:134` | cup 積の次数つき乗法を上の単位と同じ所に置く。 |
| `HomologicalAlgebra/Ext/LocalCohomology.lean:367` | 係数制限した複体のホモロジー保存の共用。 |
| `KST/NonConnective/SequentialCandidatePiColimitExchange.lean:22` | 群の余極限を既存の離散・逐次 shape の供給から使う。 |
| `KST/NonConnective/SequentialFilteredExchange.lean:26` | Ω スペクトルの filtered shape の余極限を存在結果の近くで束ねる。 |
| `KST/NonConnective/SequentialLevelColimitFunctor.lean:27` | 同じ存在結果を逐次 shape に特殊化できるか調べる。 |
| `KST/Spectra/RationalLevelCochains.lean:26` | `ULift ℚ` の `CharZero` を標準の持ち上げ結果に寄せる。 |
| `KST/Spectra/RationalLevelNormalizedCochains.lean:27` | 上と同じ `CharZero` の供給を使う。 |

## 6. 実施順と取り込み単位の案

1. KST/Spectra を起点に Ω スペクトル475件と基点付き単体集合102件の豊穣構造を登録する。提供元を一つにし、局所宣言の単純な再登録から外す。写像空間の Kan 性109件は、対象と豊穣構造を特定して次の組にする。
2. EInfinity/BarrattEccles のモデル77件とその分解65件。モデルを選ぶ scope に使い手をそろえ、同じモデルに対する cofibration・factorization の提供を照合する。停止経路の利用ファイルを組の検査対象に含める。
3. AlgebraicGeometry の Rees 群は閉商の次数付き環56件、商加群51件、スカラー塔41件から始める。商・部分加群・係数変更・全体加群を単位にする。同じ対象の `SMul`、`Module`、`IsScalarTower` は一組にし、グレーディングのデータはその提供元と組にする。
4. HomotopicalAlgebra の Reedy 模型45件と複体の模型は、基礎モデルを指定した scope ごとに扱う。左ファイブレーションの引戻しと安定 ∞ 圏の有限極限は、前提の探索を共有する単位ごとに分ける。
5. BhattScholze・KST・HomologicalAlgebra を含む導来圏675件では、主張の一般化と証明内の置き直しを個別に扱う。条件付きの残りと AR-W1 A1 (i) の登録は、それを供給する既存の補題を起点に組む。

最初は一つの提供元と代表12〜14ファイルを一組とする。囲った範囲の型と instance の選択を照合した後、利用箇所全体を同じ依存の向きで移す。確定しない群と、試しで失敗・選択変更が見つかった群は、登録の条件を決めるまで別の扱いとする。段2の組を取り込む際の全体検査は調整役の枠に合わせる。
