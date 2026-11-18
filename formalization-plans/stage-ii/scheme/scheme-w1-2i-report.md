# SC-W1 2i：進捗・検証・引き継ぎの記録

**停止点2i：完了。⑥のレーンを閉じる。** 一覧：済み71／全体71（うち追加5）、未完0。31モジュール、本体・入口2,330行、検証スクリプト込み2,437行／外枠9,000行。対象ビルド・正本の型チェック・所有195宣言の公理監査が成功。取り込みとroot・全監査は調整役が行う。以下の初期の節は経過の記録で、最終状態は末尾の引き継ぎが正本。

2026-11-17、math/scheme。ユーザー承認と指示書末尾の追記に従い、2iの外枠9,000行、66署名の範囲内で進める。約4,500行で止まらずに途中報告する。新しい数学でない照合・合成則は、元の署名・仮定を変えず、一本の補正後上端800行以内・main本体の変更なしなら紙と台帳へ追記して進む。上端が9,000行を超えそうなときは枠を上げず、完成した署名のまとまりで区切って検証済みをコミットし停止する。

## 再開と初期束（c3bbe3c81）

- 調整役がroot・全監査・sorry閉包を確認したmain **1fb2c6dcc** を fast-forward で取り込んだ。2h出口の対象ビルドも成功。2iの計数の基準はこの取り込み点。
- 正本 [署名の紙](scheme-w1-2i-route.md)・[66署名のデータ](scheme-w1-2i-signatures.json) を保ち、最初の10定義を実装した。最終有限族・元の積への一射・増大Čech・rankの試験・任意の完全係数を保持する。
- **一覧：済み10／全体66（うち追加0）。** 完了ID：T00〜T05、U01〜U03、O07。残り56署名。2iの公開署名・仮定・最終型の変更なし。既存main宣言の本体の変更なし（入口へのimport登録のみ）。
- 本体 `SerrePositivity/AlgebraicGeometry/ArcRouteB/Definitions.lean` 90行、入口2行、**実測92行／9,000行**。削除相殺なし。所有12宣言（private・生成補助を含む）の公理閉包は標準三公理のみ。
- 原稿の対象型検査、原稿・本体の同一バイトとSHA、Definitionsと直接のimporterの対象ビルド（5,417ジョブ）、別の鍵での所有監査が全て成功。各鍵は --class impl --wait 3600。一回のビルド・監査ごとに解放。rootと下流全ビルドは行っていない。
- 見込みの更新：完了分を実測へ置き換え、残りに紙の係数2と登録予備を保つと、完成見込み **3,710〜8,698行**。外枠内。未検証原稿の行を完了分として数えていない。

| ID | 宣言 | 主張 |
| --- | --- | --- |
| T00 | ValuativeCoverFamily | AGの既存の付値判定を同じ量化の別名で使う |
| T01 | IsVCoverFamily | rankの制限のない有限族のv判定 |
| T02 | IsArcCoverFamilyCharP | 元と拡大の付値環をともにrank≤1で試す |
| T03 | affineFamilyCech | 元の有限族の積への射の増大conerve |
| T04 | BS17VCechInput | 2hを受ける正本と同じ有限族のv完全性 |
| T05 | ArcRouteBGoal | 正本と同じ有限族のarc完全性の最終型 |
| U01 | arcBaseChangeHom | 元の二つの射のtensorの指定構造射 |
| U02 | PerfectRingCechUniversalExact | 全ての完全係数の底変換後でのČech完全性 |
| U03 | IsArcHom | 一射のrank≤1の付値判定 |
| O07 | GoodArcInterval | 指定区間環の完全な全係数での完全性 |

## 作業木・次の束

未検証原稿は formalization-plans/stage-ii/scheme-drafts/ に置き、コミットしていない。被覆の法則U04〜U06、Frobenius完全化M01〜M04・I00・P00、普遍係数の法則U07〜U09、既存模型のUnderへの移送M05〜M07、区間の照合I01〜I03、弱NullstellensatzのQ01、正本の条件付き比較T06・V01〜V06を検証待ちの原稿として用意した。これらを済みの署名には数えない。次は被覆の法則の対象検証。各束の通過後に本体へ移し、直接のimporter・所有監査を経てコミットする。

## 完了時に残す引き継ぎ

まだ2iの停止点ではない。完了時には、この記録を最終の済み・未完の一覧、実測、使用する側との型の一致、全対象ビルドと所有監査、BS17の対応表に書くpartialの差（n=1・E=O・affine・完全F_p代数の有限族）、作業木の未コミットの有無で更新する。BM18 Thm1.7・∞・一般W_n・有限射影E・非affineは作らない。2i完成でレーンを閉じ、取り込みは調整役が行う。


## 被覆の法則の束（777a9e2f1）

**一覧：済み13／全体66（うち追加0）。** U04〜U06を追加で閉じた。`isArcHom_pi_iff` は元の有限族の積への一射とrank条件を保った付値判定との同値、`isArcHom_baseChange` は同じ付値拡大をtensor liftへ渡す底変換、`isArcHom_of_refinement` は元の射と可換な細分からの判定の移送。

原稿の型検査、本体への同一バイト・SHA、CoverLawsと直接のimporterの対象ビルド（5,419ジョブ）、別の共有鍵での所有3宣言の公理閉包が全て成功。標準三公理のみ。本体66行・登録2行を追加し、初期束と合わせ**実測160行／9,000行、所有15宣言**。公開署名・仮定の変更、一覧への追加、既存main本体の変更なし。

完了分を実測へ置き換えた完成見込みは **3,672〜8,520行**。半分の4,500行には未到達。次の5モジュール（FrobeniusPerfect・UniversalCech・ModelUnder・IntervalSpectrum・FpResiduePoint）は対象ビルド中の未検証候補で、未コミット。今回から独立した数本を一回の小さい対象ビルドにまとめ、通過後に同一バイト・SHAと別鍵の所有監査を確認してコミットする。共有の整理券は一つだけ。


## 照合・合成則L01の追加（11-17夕の事前承認）

[台帳](scheme-w1-2i-law-ledger.md) に完全な型・原典上の位置・依存・見込みを記録した。既存の押し出しの合成法則を指定Arrow同型に束ねるだけで、新しい数学ではない。元の署名・仮定・既存main本体は変更しない。素30〜90行、係数2の上端180行≤800。追加後は一覧：済み13／全体67（うち追加1）、補正後の完成見込み 3,732〜8,700行で外枠内。記録後は止まらず実装する。


## 完全化・普遍係数・模型・区間・剰余体の点（7c49cb0a2）

**一覧：済み29／全体67（うち追加1）。** 追加でM01〜M07・I00〜I03・P00・Q01・U07〜U09を閉じた（16署名）。L01は記録・原稿までで、まだ完了数へ含めない。

| モジュール | ID | 到達した主張 | 本体行数 | 所有宣言 |
| --- | --- | --- | ---: | ---: |
| FrobeniusPerfect | M01〜M04・I00・P00 | 実際のFrobenius順極限は完全、完全な値域へ元の段0を保って延長、模型の単位と任意積の完全性 | 97 | 12 |
| UniversalCech | U07〜U09 | 任意の完全係数への普遍完全性の再底変換、忠実平坦な拡大上の切断による反映、零環を含むtensorの完全性 | 114 | 3 |
| ModelUnder | M05〜M07 | 元の有限表示SmallModelと指定脚をUnderに保ち、その同じ余錐の余極限性 | 56 | 9 |
| IntervalSpectrum | I01〜I03 | 指定区間環とスペクトルの閉区間の順序同型、隣接点の次元≤1、全区間の元の環への同型 | 98 | 24 |
| FpResiduePoint | Q01 | 非零な有限型代数の代数閉係数体への点 | 34 | 1 |

本体399行・入口10行を追加し、**実測569行／外枠9,000行**。5モジュールと直接のimporterの対象ビルド（5,425ジョブ）、原稿と本体の同一バイト・SHA、別の共有鍵での全所有49宣言の監査が成功。前の15宣言と合わせ**所有64宣言、標準三公理のみ**。署名の型・仮定の変更、既存main本体の変更なし。

U07はAlgebra.TensorProduct.cancelBaseChangeの型とカテゴリー側のtensorの加群構造の違いを直接castせず、既存のtensorProdIsoPushoutとUnder.pushoutCompで同じUnderの構造射を保つArrow同型を作ってからconerveへ送った。U08は忠実平坦な係数を、同じUnder対象の代数構造で与えて反映した。選ばれたČech余極限の内部の書き換えを避けている。これは元の公開署名内の証明で、main本体の置換はない。

完了分を実測へ置き換え、未完には紙の係数2と登録予備を保った完成見込みは **3,417〜7,329行**。4,500行には未到達。次の9モジュールは対象ビルド待ちの未検証候補であり、完了数・実測へ含めない。


## 模型の余極限・端点の切断・付値試験への比較（03338bc40）

**一覧：済み49／全体67（うち追加1）。** L01、I04〜I07、P03〜P05、T06、V01〜V06、M08〜M12の20署名を閉じた。

| モジュール | ID | 到達した主張 | 本体行数 | 所有宣言 |
| --- | --- | --- | ---: | ---: |
| BaseChangeComparison | L01 | 指定した係数の可換三角形の、一回と二回の底変換のArrow同型 | 49 | 5 |
| EndpointSections | I05・I06 | 左右の非退化区間への同じ基底上の有限表示の因子化 | 95 | 2 |
| ProbeTerms | P03〜P05 | 正次数の第0因子の係数射・合成の法則・二回の底変換との指定Arrow同型 | 51 | 7 |
| IntervalPoints | I04・I07 | 有限表示模型の剰余体上の点、完全化への延長からの普遍完全性 | 83 | 2 |
| ProbeComparison | T06・V01〜V06 | 2hの入力、一射・零環・probe product・完全係数・B1の条件付き比較 | 141 | 8 |
| FilteredUniversalCech | M12 | 指定したfiltered余錐に全ての完全係数での完全性を戻す | 56 | 1 |
| PerfectedModelDiagram | M08 | 同じSmallModelの実際のFrobenius順極限の図式 | 64 | 10 |
| PerfectedModelCocone | M09・M11 | 元の完全環への指定脚、その脚によるarc被覆の細分 | 68 | 6 |
| PerfectedModelColimit | M10 | 既存の二変数の交換で同じ余錐の余極限性を得る | 56 | 15 |

本体663行・登録18行を追加し、**実測1,250行／外枠9,000行**。全9モジュールと直接のimporterの対象ビルド（5,441ジョブ）、原稿・本体の同一バイトとSHA、別鍵の全所有56宣言の監査が成功。合計**所有120宣言、標準三公理のみ**。heartbeatなどのリソース上限は上げていない。切断の接続では元のAlgHomのRingHomと可換性を先に保存し、派生した代数構造との取り違えを避け、射を明示して型推論の探索を減らした。

元の66署名の型・仮定の変更なし。追加は事前承認された照合法則L01だけで、記録した型のまま検証した。mainの既存本体は変更していない。全て新規のArcRouteBモジュール（入口登録のみ）。

残りは **O01, O02, O03, O04, O05, O06, O08, O09, I08, I09, I10, I11, I12, P01, P02, P06, B01, B02** の18署名。完了分を実測へ置き換え、残りに係数2と登録予備を保つと完成見込み **3,000〜5,406行**。約4,500行には未到達。区間の三つのtensor比較O01〜O03と係数の短複体O04は次の対象ビルド中で、完了数にはまだ含めない。


## 区間の係数比較と短複体（153540e07）

**一覧：済み53／全体67（うち追加1）。** O01〜O04を閉じた。`intervalTensorLocalizationEquiv` は同じ区間上の局所化、`intervalTensorQuotientEquiv` は下端の商、`intervalTensorIntersectionEquiv` は重なりの区間環を、それぞれ元のV上のAlgEquivとして比較する。両方向の構造射を既存の区間の普遍性から作り、V上の射の一意性で両逆を示した。新しい区間や模型を選んでいない。

`overlapTensorModuleComplex` は任意のTで、T→(T⊗V V_b)×(T⊗V V/a)→T⊗V V[a,b]という同じ単位・制限の差の短複体を与える。この構成自体ではTの完全性・平坦性は要求していない。短完全性O05はまだ未完。

本体はIntervalTensorComparison 123行・OverlapComplex 45行、登録4行を追加し、**実測1,422行／外枠9,000行**。対象2モジュールと直接のimporterのビルド（5,760ジョブ）、同一バイト・SHA、別鍵の所有53宣言の監査に成功。合計**所有173宣言、標準三公理のみ**。署名の型・仮定・既存main本体の変更なし。

完成見込みは、完了分を実測へ置き換えた係数2と登録予備込みで **2,822〜4,728行**。4,500行には未到達。O08・I08の対象ビルドは通過したが、左右の延長I09/I10とO05の候補を再検証中で、監査・コミットまでは完了数へ含めない。


## 照合法則L02の追加（11-17夕の事前承認）

[台帳](scheme-w1-2i-law-ledger.md) に環射とUnderからの同じ底変換のArrow比較L02を記録した。新数学・元の型や仮定・main本体の変更はなく、補正上端140行≤800。元の66署名に照合2本を加え、一覧：済み53／全体68（うち追加2）。確定分だけを使った完成見込み2,862〜4,868行で外枠内。記録後は事前承認に従い進める。


## 既存の係数構成の法則L03・L04の抽出

[台帳](scheme-w1-2i-law-ledger.md) に完全な型を記録した。既存の区間環と剰余体の証明で構成済みの商の根・局所化の根と分母の計算を、同じ係数の法則として名前付きで抽出する。元のO06の型・仮定を変えず、既存main本体も変更しない。一本の補正上端160行≤800で、新しい数学の供給ではなく既存構成の係数移送の分割。追加後の一覧：済み53／全体70（うち追加4）、完成見込み2,962〜5,188行で外枠内。


## 同じmoduleCechの係数検出の分割L05

O06で予定した既存APIの適用をL05として型付きで[台帳](scheme-w1-2i-law-ledger.md)へ記録した。O09でも同じT上の列を使う。新数学・元の型や仮定・main本体の変更なし、補正上端240行≤800。追加後は一覧：済み53／全体71（うち追加5）、完成見込み3,062〜5,428行で外枠内。


## 区間の制限・左右の延長と重なりの短完全性（11-17夜）

**一覧：済み61／全体71（うち追加5）。** O05・O08・I08〜I10・L02〜L04を検証した。IntervalRestrictions（61行）は良い区間の制限とrank≤1の場合、LocalExtensions（84行）は左右の局所延長、OverlapShortExact（84行）は任意の完全T上の同じ係数列の短完全性を与える。BaseChangeArrowComparison（29行）は環射のAlgebra構造と指定Under底変換のArrowを比較し、IntervalCoefficientPerfect（56行）は既存の商・局所化の根の構成を抽出する。

本体314行・入口登録10行を加え、**実測1,746行／外枠9,000行**。5モジュールと直接importerの対象ビルド（5,765ジョブ）が成功。同一バイトとSHAを確認し、別鍵の全所有9宣言の監査も標準三公理のみで成功した。累計所有182宣言。既存main本体・元の66署名の型や仮定は変更していない。完成上端は前報の5,428行以内を維持し、4,500行には未到達。残りはO06・O09・I11・I12・P01・P02・P06・B01・B02・L05の10署名。貼り合わせと全区間への復帰の候補は未検証下書きであり実測に含めない。


## 普遍貼り合わせと全区間（fddd1a4cd）

**一覧：済み65／全体71（うち追加5）。** L05・O06・O09・I11を閉じた。OverlapCoefficientDetection（55行）は任意の完全T上の同じ短完全列をmoduleCechへ適用する。UniversalOverlap（76行）は三つの指定した底変換から普遍完全性を検出する。IntervalGluing（94行）はO01〜O03の元のV上の同型とL01/L02を使い、任意の完全な全区間係数Tで二つの良い区間を貼る。PerfectedFpArc（67行）はBM18 Lemma 4.7のpoint/sub/right/left/glueを埋め、全区間の指定AlgEquivで元の付値環へ戻す。

本体292行・登録8行を追加し、**実測2,046行／外枠9,000行**。4モジュールと直接importerの対象ビルド（5,771ジョブ）、同一バイト・SHA、別鍵の所有4宣言の監査が成功。累計所有186宣言、標準三公理のみ。元の66署名・既存main本体の変更なし。残りはI12・P01・P02・P06・B01・B02の6署名で、現在の完成上端は5,428行以内。最終型を正本からそのまま抜き出した独立した利用側のチェックも用意した（未検証）。


## 停止点2i：最終の検証と引き継ぎ

数学・検証スクリプトのコミット：`7d6355ce5`。基準はmain `1fb2c6dcc`。**一覧：済み71／全体71（うち追加5）、未完0。** 最初の66署名は9c8beeaf6の完全な型と機械照合して全て一致し、追加は記録済みの照合・分割L01〜L05だけ。型・仮定や既存mainの数学の本体の変更はない。

### 出口と証明の接続

`SerrePositivity.AlgebraicGeometry.ArcRouteB.cech_exact_of_arcCover_perfect` @ `SerrePositivity/AlgebraicGeometry/ArcRouteB/ArcCoverCech.lean` が出口。完全F_p代数の有限族、元の積への一射、増大Čechの型を保つ。零環・空の族も除いていない。

同じ有限表示模型を完全化し、端点の切断・区間の制限・左右の延長・重なる区間の貼り合わせを通して、絶対整閉付値環上の普遍Čech完全性へ進む。任意の完全T上の重なりの短完全列とTor消滅を使うので、Tの基底上の平坦性は仮定しない。模型の指定余錐のfiltered余極限、超積の平坦底変換と加群の零性の検出から、付値probeの積上の普遍完全性を得る。probeのČechの正次数の第0因子の脚と二回の底変換を比較し、2hの出口とB1の二重Čech比較へ渡す。

既存の本体B1〜B5（被覆・Tor・重なりの短完全列・区間判定・超積・付値probe）を使う。G-A6-1cの`valuationRing_milnorSquare_perfect`は本体にあり、今回の一般の重なりではその供給側の既存のoverlap短完全列とTorのAPIを直接使った。BM18 Thm1.7の一般の∞圏値の層判定は使っていない。

### 検証・規模

- 31モジュールは全て`AlgebraicGeometry/ArcRouteB/`に置き、入口`SerrePositivity/AlgebraicGeometry.lean`へ登録した。元の入口は同一バイトの接頭辞のまま、末尾のimport登録だけを足した。
- 最終対象ビルド：ArcCoverCechと直接importer、**5,778ジョブ成功**（`scheme-drafts/2i-arc-exit-native-4.log`）。root・下流全ビルドは実施していない。
- 再実行可能な小さい検証：`lake env lean formalization-plans/stage-ii/scheme/scheme-w1-2i-verify.lean`。正本drafts/A6/ArcRouteB.leanの定義とArcRouteBGoalをそのまま別名前空間へ抜き出し、出口を実際に適用して型を確認した。未完成drafts全体へのimportや、型を弱める置き換えはない。
- 同じ検証で31モジュールの全所有195宣言（private・生成補助を含む）の公理閉包が成功。**標準三公理のみ**：propext、Classical.choice、Quot.sound。sorry・新しい公理・native_decide・リソース上限の増加なし。
- 本体2,268行＋入口62行＝**2,330行**。検証スクリプト107行を含めても**2,437行／9,000行**。4,500行の途中報告基準へ達する前に完成した。完了後の追加見込み0。
- 全て共有鍵`with_build_lock.sh --class impl --wait 3600`、待ちは一つ、ビルド・監査の間だけ保持。ファイル記述子不足で待機プロセスが二度終了したが、Leanを起動していないことを確かめてから同じ共有鍵で取り直し、最終ビルドと検証は成功した。

ソースごとのSHA・行数・所有宣言数、71署名の置き場所は[検証データ](scheme-w1-2i-verification.json)に記録した。公開宣言の型は[署名の紙](scheme-w1-2i-signatures.json)、追加法則は[台帳](scheme-w1-2i-law-ledger.md)。

### BS側への引き継ぎと範囲

- `formalization-plans/bhatt-scholze/drafts/A6/ArcSheafProperty.lean`のG-A6-1、`cech_exact_of_arcCover_perfect`のsorryは、本体の同名の出口を完全修飾して適用すれば置き換えられる。型は正本のArcRouteBGoalと同じ。BS側のdrafts自体は編集していない。
- G-A6-1aは2hの`cech_exact_of_vCover_perfect`で供給済み。G-A6-1cは既存の本体。G-A6-1b（BM18 Thm1.7の一般の∞圏の主張）のsorryはこの経路では使わず、完成とはしない。
- BS17 Thm4.1の対応表は**partial**のまま。今回の供給はaffine・構造層（n=1、E=O）・完全F_p代数の有限族のv/arc Čech完全性。一般のW_n、有限射影E、非affineの一般性は未実装で、⑧の対応表へこの差を引き継ぐ。
- 71署名は全て検証済みで、未完0。このレーンの追加作業はない。調整役によるmainへの取り込み、rootと全監査は別に行う。
- 最終報告のコミット後、追跡ファイルの未コミット差分は0となる。`scheme-drafts/`には作業用の原稿・ログ・スクリプトが未追跡で残る。取り込み対象に含めず、検証済み本体は全てコミット済み。

### 最終一覧

| ID | 宣言 | 置き場所 |
| --- | --- | --- |
| U01 | `arcBaseChangeHom` | Definitions.lean:60 |
| U02 | `PerfectRingCechUniversalExact` | Definitions.lean:69 |
| U03 | `IsArcHom` | Definitions.lean:75 |
| U04 | `isArcHom_pi_iff` | CoverLaws.lean:21 |
| U05 | `isArcHom_baseChange` | CoverLaws.lean:40 |
| U06 | `isArcHom_of_refinement` | CoverLaws.lean:58 |
| U07 | `perfectRingCechUniversalExact_baseChange` | UniversalCech.lean:24 |
| U08 | `perfectRingCechUniversalExact_of_flat_factor` | UniversalCech.lean:77 |
| U09 | `perfectTensor_of_primeCast_eq_zero` | UniversalCech.lean:54 |
| M01 | `frobeniusDirectLimit_primeCast_eq_zero` | FrobeniusPerfect.lean:18 |
| M02 | `frobeniusDirectLimit_perfectRing` | FrobeniusPerfect.lean:24 |
| M03 | `frobeniusDirectLimitDesc` | FrobeniusPerfect.lean:57 |
| M04 | `frobeniusDirectLimitDesc_comp_of_zero` | FrobeniusPerfect.lean:66 |
| M05 | `finitePresentationModelUnderDiagram` | ModelUnder.lean:21 |
| M06 | `finitePresentationModelUnderCocone` | ModelUnder.lean:35 |
| M07 | `finitePresentationModelUnderCoconeIsColimit` | ModelUnder.lean:49 |
| M08 | `perfectedModelDiagram` | PerfectedModelDiagram.lean:21 |
| M09 | `perfectedModelCocone` | PerfectedModelCocone.lean:21 |
| M10 | `perfectedModelCoconeIsColimit` | PerfectedModelColimit.lean:25 |
| M11 | `perfectedModel_isArcHom` | PerfectedModelCocone.lean:59 |
| M12 | `perfectRingCechUniversalExact_of_filtered_models` | FilteredUniversalCech.lean:24 |
| I00 | `perfectedAlgebraUnit` | FrobeniusPerfect.lean:82 |
| I01 | `intervalRingSpectrumOrderIso` | IntervalSpectrum.lean:20 |
| I02 | `intervalRing_krullDim_le_one_of_no_prime_between` | IntervalSpectrum.lean:48 |
| I03 | `intervalRingOfFullSpectrumEquiv` | IntervalSpectrum.lean:71 |
| I04 | `exists_fp_residue_point_of_perfectedArc` | IntervalPoints.lean:25 |
| I05 | `exists_right_interval_fp_section` | EndpointSections.lean:20 |
| I06 | `exists_left_interval_fp_section` | EndpointSections.lean:58 |
| I07 | `perfectedAlgebraUnit_universalExact_of_section` | IntervalPoints.lean:51 |
| O01 | `intervalTensorLocalizationEquiv` | IntervalTensorComparison.lean:24 |
| O02 | `intervalTensorQuotientEquiv` | IntervalTensorComparison.lean:63 |
| O03 | `intervalTensorIntersectionEquiv` | IntervalTensorComparison.lean:102 |
| O04 | `overlapTensorModuleComplex` | OverlapComplex.lean:24 |
| O05 | `overlapTensorModuleComplex_shortExact` | OverlapShortExact.lean:27 |
| O06 | `perfectRingCechUniversalExact_of_overlap` | UniversalOverlap.lean:27 |
| O07 | `GoodArcInterval` | Definitions.lean:85 |
| O08 | `goodArcInterval_sub` | IntervalRestrictions.lean:24 |
| O09 | `goodArcInterval_glue` | IntervalGluing.lean:29 |
| I08 | `goodArcInterval_of_rank_le_one` | IntervalRestrictions.lean:45 |
| I09 | `goodArcInterval_right` | LocalExtensions.lean:23 |
| I10 | `goodArcInterval_left` | LocalExtensions.lean:54 |
| I11 | `perfectedFpArc_universalExact` | PerfectedFpArc.lean:31 |
| I12 | `aicValuationArc_universalExact` | AicValuationArc.lean:33 |
| P00 | `perfectRing_pi_of_primeCast_eq_zero` | FrobeniusPerfect.lean:91 |
| P01 | `perfectRingCechUniversalExact_of_ultraproducts` | UniversalUltraproduct.lean:30 |
| P02 | `aicValuationProductArc_universalExact` | AicProductArc.lean:30 |
| P03 | `probeCechFirstFactor` | ProbeTerms.lean:22 |
| P04 | `probeCechFirstFactor_comp` | ProbeTerms.lean:30 |
| P05 | `probeChangeToTermIso` | ProbeTerms.lean:38 |
| P06 | `probeArc_positiveRows` | ArcCoverCech.lean:33 |
| T00 | `ValuativeCoverFamily` | Definitions.lean:22 |
| T01 | `IsVCoverFamily` | Definitions.lean:28 |
| T02 | `IsArcCoverFamilyCharP` | Definitions.lean:33 |
| T03 | `affineFamilyCech` | Definitions.lean:38 |
| T04 | `BS17VCechInput` | Definitions.lean:44 |
| T05 | `ArcRouteBGoal` | Definitions.lean:52 |
| T06 | `bs17VCechInput` | ProbeComparison.lean:24 |
| V01 | `cechExact_of_affineVCover_from_BS17` | ProbeComparison.lean:29 |
| V02 | `cechExact_of_perfectAffineVCover_from_BS17` | ProbeComparison.lean:49 |
| V03 | `cechExact_valuationProbeProduct_from_BS17` | ProbeComparison.lean:78 |
| V04 | `isAffineVCover_tensor` | ProbeComparison.lean:87 |
| V05 | `cechExact_valuationProbeProduct_tensor_from_BS17` | ProbeComparison.lean:103 |
| V06 | `cechExact_of_valuationProbeTests` | ProbeComparison.lean:120 |
| B01 | `cechExact_of_arcHom_perfect` | ArcCoverCech.lean:70 |
| B02 | `cech_exact_of_arcCover_perfect` | ArcCoverCech.lean:79 |
| Q01 | `nonempty_algHom_of_isAlgClosed` | FpResiduePoint.lean:18 |
| L01 | `arcBaseChangeTransIso` | BaseChangeComparison.lean:21 |
| L02 | `arcBaseChangeArrowIso` | BaseChangeArrowComparison.lean:20 |
| L03 | `intervalCoefficient_primeQuotient_perfect` | IntervalCoefficientPerfect.lean:18 |
| L04 | `intervalCoefficient_primeLocalization_perfect` | IntervalCoefficientPerfect.lean:35 |
| L05 | `cechExact_of_overlapTensor_coefficients` | OverlapCoefficientDetection.lean:25 |
