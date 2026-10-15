# スペクトルのレベルモデル：生成射による構成

宇宙・入力の共通契約はHomotopicalAlgebra/READMEとk-theory.md §123、実行記録は§130〜131。
実装は固定MathlibのModelCategory・MorphismProperty・small object argument上に置く。
安定モデル構造はまだ扱わない。グローバルなスペクトルモデルinstanceを登録せず、構成した値を局所instanceとして使う。

| 入口 | API |
| --- | --- |
| LevelClasses | levelProperty K P、levelGenerators K P、free/evaluationでのrlp計算 |
| LevelRecognition | levelModelCategory K I J hacyclic。像のSOAとJ-cell acyclicityから構成。レベルW/Fib、生成性、評価/freeのQuillen性、両関手的分解 |
| LevelAcyclicity | 評価した自由J生成射がtrivial cofibrationならfree J-cellはレベル弱同値 |
| LevelSmallness | 小さい生成射クラスと共通のregular presentability cardinal κから、全次数free像のIsCardinalForSmallObjectArgumentとSOAを証明 |
| LevelFromGenerators | levelModelCategoryOfGenerators K I J κ hI hJ heval。前二行の検証を構成内で行い、W/Fibの一致と生成性を提供 |

smallnessの宇宙w、対象の宇宙u、射の宇宙vは独立。
源Cには小さい極限余極限、wサイズ余極限、生成モデル構造を要求する。
κはCardinal.{w}でregular。スペクトル圏のLocallySmall.{w}も入力に記録する。
共通κでの生成射始域のpresentabilityと、評価した自由J生成射のtrivial cofibration性は具体的に検証する条件。

検証：`check_spectrum_level_classes`, `check_spectrum_level_model`, `check_spectrum_level_generators`。
最後のスクリプトは像のSOA/cell acyclicityを仮定せず、構成・生成性・関手的分解を利用する。
内部補助を含む39宣言の公理監査、既存StageTwo・H5との同時import検証が成功。
全スペクトル・共通基盤監査は276モジュール2759公開宣言。標準公理のみ、sorry・引用依存なし。

コミット：lifting `ae733ed`、認識 `3e928f5`、生成射からの構成 `4dbdaf1`。
具体的PSS/円の条件検証、多対象加群・SM7、一般作用・cotensor・豊穣構造は後続。

## 生成射テストの証明（§132）

`FreeLevelCofibrations`は評価した自由trivial cofibrationを、thinな誘導添字とcofibrant tensor冪から証明する。
`MonoidalLevel.levelModelCategoryOfMonoidalGenerators K I J κ hI hJ`は追加の生成射テストなしでレベルモデルを構成する。
源CのQuillen bifunctor tensor、cofibrant unit/Kと共通のpresentability boundは入力に明記する。
この定理はスペクトル自身のmonoidal/SM7条件の証明とは別である。

`check_monoidal_level_model`は構成・生成性・評価のQuillen性・関手的分解と空の場合も含む添字のthin性を検証。
共通補題とレベル実装の全72宣言が標準公理のみで監査成功。
コミット`9c86d7f`, `2165b14`。具体的PSSとSM7・作用・豊穣の接続は後続。

## 具体的単体的入力と基点付き生成射（§145〜§146）

SimplicialGeneratorsは実際の境界I・horn Jの共通aleph0-presentabilityとSOAを提供する。
SimplicialCofibrancyは固定mono cofibrationクラスで全PSSと既存circleのcofibrancyを証明する。
PointedGeneratorsは自由基点追加のstrict像pointedI/Jのrlp、共通presentabilityとSOAを接続する。
忘却のfiltered colimit保存を使い、全余極限保存を仮定しない。

これらは完成したKan–Quillen ModelCategoryを仮定せず、Wも導入しない。
ModelCategory全体とanodyne/trivial cofibration比較は固定MathlibでTODOのため、後続の接続が必要。
check_simplicial_model_inputs.leanはその区別を保った利用例と26宣言の公理監査を含む。
コミット73e55b0・51d0f66・a5d2575。


## S0完了：一般C,Kのcombinatorialレベルモデルと左固有性（2026-10-16）

`Combinatorial`は実際のDay対称列とSym(K)上の内部加群に対して局所可呈示性を証明する。
小さい強生成族と既存の自由・忘却随伴、忘却の余極限創出・同型反映を使う。
この局所可呈示性にはモデル構造もKのcofibrancyも不要。
`exists_combinatorial_levelModel`はCの局所可呈示性・生成表示と評価した自由J生成射の計算から、
実際のレベルモデルと三クラス・生成表示を構成する。スペクトル上のSOAや基数を入力しない。

`LeftProper`は評価した自由I生成射のcofibration性を、超限合成とretractを含む生成左クラスへ拡張する。
源の左固有性から実際のレベルモデルの左固有性を得る。cofibrantな端点のみに制限しない。
一般入口の評価テストは、pushout-productと単位・Kのcofibrancyから供給できる。
単位cofibrancyはこの十分条件に限定され、局所可呈示性と一般評価テストの入口には不要。
`exists_leftProper_combinatorial_levelModel`は実際のモデル・三クラス・生成表示・左固有性を同時に出力する。
受入`check_spectra_presentability`（7宣言・3モジュール）、`check_spectra_level_left_proper`
（14宣言・4モジュール）、段階2回帰と共有公理監査が成功。新規sorry・引用axiomなし。
実装`2c53a5b0`・`91c43b23`。S1〜S3は引き続き未完了。


## S1進捗：実際の局所化射とRMapテストの計算（2026-10-16）

`General/Suspension`は一般Kの懸垂構造射と随伴構造射を構成し、スペクトル射に関する自然性を証明する。
`Stable/LocalizingMaps`は実際のF_(n+1)(A⊗K)→F_n(A)、入力に関する自然性と小さい族からの射クラスを構成。
`CofibrantLocalizingMaps`はQ(A)を用いる場合も含め両端点のcofibrancyを証明する。
`LocalizingHom`は任意のcosimplicial対象について、局所化射のHomと随伴構造射のHomのArrow同型を構成。
`FrameLocality`は実際の自由source frameと共有`FrameArrowTests`を使い、元の通常の局所対象の述語を、
スペクトルのfibrant replacementの各段の随伴構造射によるHomテストとして計算する。
`Omega`の述語はCの元の弱同値で独立に定義し、レベルfibrant対象間のレベル弱同値に関する不変性を証明。

`check_spectrum_stabilization_maps`の38宣言・7モジュールの公理監査、S0・段階2・豊穣検出の回帰確認が成功。
新規sorry・引用axiomなし。実装`42d28824`・`3c9a992b`。
S1全体は未完了。残るのは小さいホモトピー生成族の検出との接続と局所fibrant↔Ω_Kの最終同値。
S2・S3は引き続き未完了。計画§215に証明済みの範囲と残る手順を明記した。


## S1完了：局所fibrant対象とレベルfibrantなΩ_K対象（2026-10-16）

`LevelFacts`は実際のレベル弱同値・fibrationの同定から評価・自由関手のQuillen性と
fibrancyの各段による判定を証明する。`Stable/OmegaDetection`は既存の通常の局所性を、
実際のRSp(E)の随伴構造射のHomテストとして計算し、小さい検出族によってΩ_K条件へ移す。
fibrant Eについては、実際のreplacement単位を評価した弱同値とΩ_Kの不変性でE自身へ戻す。

`OmegaLocalObjects.exists_omega_localizingMaps`は、一般C,Kと元のレベルクラス・指定分解から、
小さいcofibrant族、実際の局所化射の小ささと両端点のcofibrancy、全Eの局所fibrant↔Ω_Kを同時に出力する。
検出族とその検出能力はCのcombinatorial性から構成し、入力に戻さない。
`check_spectrum_omega_local_objects`ではS0のモデルと両分解も構成する最終利用例を検証した。
11宣言・5モジュールの公理監査、§215の38宣言・7モジュール、L1・段階2の回帰が成功。
新規sorry・引用axiomなし。実装`e123a735`・`c2aaa9ee`。計画§216でS1完了。
S2の実際の安定局所化モデルとS3の通常の安定性の比較は引き続き未完了。


## S2進捗：実際のK局所モデルと元レベルmonoidal/SM7（2026-10-16）

`Stable/ModelCategory.exists_stableModelPresentation`はS1の小さい実際の射へ一般L4を適用し、
実際のモデル、元cofibration・局所同値・右持ち上げの三クラス、生成表示、Ω_Kのfibrant判定を構成する。
左固有性と構成後のaccessibleな両因子分解も取得できる。
`Stable/Replacement`は実際のaccessibleなLと単位ηを構成し、値がレベルfibrantなΩ_K対象であり、
K局所モデルの弱同値がLによる元レベル弱同値の逆像だと証明する。
S0の`exists_leftProper_levelModel_of_monoidal`は源のmonoidal条件から評価生成射の計算を供給する。

`GeneralLevelTensor`は一般C,Kの自由テンソル・pushout-productのArrow比較から、元レベルモデルの
pushout-productを証明する。Cの単位がcofibrantなら、free-zero単位比較により実際のmonoidal modelを得る。
`GeneralLevelEnriched`は既存の実際のC作用、cotensor、eHomにQuillen/SM7条件を供給する。
作用のunit axiomもcofibrantなCの単位という明示的な十分条件で取得する。

K局所モデルの受入30宣言・3モジュール、元レベルmonoidal/SM7の受入26宣言・4モジュール、
S0・S1・段階2の回帰と共有公理監査が成功。新規sorry・引用axiomなし。
実装`74321dae`・`99e09cc7`。計画§217に入力と出力を明記した。
S2全体は未完了。局所化後のtensor適合性とmonoidal/SM7への接続が残り、S3も未完了。


## S2完了：実際の局所tensor適合性と局所monoidal/SM7（2026-10-16）

`Stable/InternalHomOmega`は一般Kの構造射の直接公式から、自由cofibrant係数の内部Homとcotensorが
レベルfibrantなΩ_K対象を保つと証明する。局所化後のモデルやSM7を先取りしない。
`TensorCompatibility`は実際の右随伴によるQuillen普遍性を使い、pointwise tensor XとF_n(X)とのtensorを
構成済みK局所モデル上の左Quillen自己関手へ延長する。元のQで置換した局所化射へのtensor適合性も出力する。

`EnrichedModel`はCの生成cofibrationの始域のcofibrancyという追加条件の下で、
これらの適合条件をE0へ供給し、局所monoidal条件と実際のC値eHom・cotensorのSM7を証明する。
`monoidal_model_of_original_unit`と`enriched_unit_of_original`は元のunit axiomを引き継ぎ、
単位のcofibrancyを仮定しない。cofibrantなCの単位からunitを供給する具体的入口もある。
生成始域の条件は豊穣・monoidal部分に限り、通常のK局所モデルと置換の存在には加えない。

最終利用例`check_spectrum_stable_enriched`はモデル・両分解・局所化射の族も構成し、
Ω_K保存・tensor適合性・局所SM7を入力せず最終結果を得る。13宣言・3モジュールを監査。
Ω_K保存30宣言・5モジュール、通常モデル31宣言・3モジュール、元レベルmonoidal26宣言・4モジュール、
一般E0・段階2の回帰と共有4368宣言・379モジュールの公理監査も成功。新規sorry・引用axiomなし。
実装`2bd07abf`・`06473b08`・`73fc5730`。計画§218でS2完了。
S3の導来K可逆性と通常の懸垂の安定性の比較、およびF1の残項目は引き続き未完了。


## S3進捗：任意係数の安定化射とtensor評価（2026-10-16）

`Stable/UniversalLocalizingMaps`は小さい検出族に限定せず、任意のcofibrant Aの
実際の安定化射を局所弱同値と証明する。局所fibrantのΩ_K判定とframe Homの
右Quillen性を使い、単位のcofibrancyは要求しない。
`Stable/TensorInverseMap`は実際の自由tensor・単位比較から
F₁(𝟙_C)⊗F₀(K)→𝟙_Spを構成し、Cの単位がcofibrantなら局所弱同値と証明する。
`check_spectrum_tensor_inverse`で利用例と7宣言・2モジュールの標準公理監査が成功。
通常モデル・局所monoidal/SM7・A0/A1の回帰も成功。実装`75864a00`、計画§219。
S3の導来可逆性・通常の懸垂との比較、およびF1の残項目は引き続き未完了。


## S3進捗：導来K可逆性とtensor/cotensorの導来同値（2026-10-16）

`Stable/DerivedTensorInverse`は§219の実際の評価射から、F₀(K)との導来tensorの
逆関手をF₁(𝟙_C)との導来tensorとして構成する。
実際のfree-zero/pointwise自然同型を導来化し、各段tensor Kが導来同値となること、
その右随伴cotensor Kの右導来が逆関手となることも証明する。
単位のcofibrancyを明示的な十分条件とし、既存の通常局所化の存在条件は変更しない。
`canonicalDerivedKTensorEquivalence`は標準の導来関手と比較射を実際に選択する。
最終入力だけから元・局所モデルと四つの導来関手を構成する利用例と、
70宣言・4モジュールの標準公理監査が成功。合同build2924 jobs、局所monoidal・段階2の回帰も成功。
共有一般論`92bb2333`、スペクトルへの適用`643a17be`。詳細は計画§220。
S3全体は未完了。PSS/S¹で通常の導来懸垂との比較と旧APIへの接続が残る。
F1の指定分解なしの任意モデル源の最終関手も引き続き未完了。


## S3進捗：円tensorのgood cylinder商と既存懸垂API（2026-10-16）

一般の基点付き圏の商pushoutと、一般スペクトルの実際の零対象を構成した。
`General/SuspensionPushout`は任意Kについて、円tensorが区間の境界tensorを
零対象へ潰す実際のpushoutであることを証明する。
`General/SimplicialCylinder`は実際のQuillen作用からcofibrant Eの区間tensorを
good cylinderと証明し、E⨿Eと境界tensorの同型・二端点包含との整合性を構成する。
円tensorはこの実際のcylinderの両端を零対象へ潰すpushoutとなる。
`SimplicialSuspensionComparison`は既存の懸垂関手との一致、ループ側の自然同型、
単位・余単位の可換式、構造射の互換性を証明する。
構成済み局所モデルの作用から取得する利用例と97宣言・6モジュールの標準公理監査、
合同build2988 jobs、前回の導来同値と段階2の回帰確認が成功。
基盤`8e7ba3ca`、幾何的比較`862040a8`。計画§221に詳細を記録。
S3全体は未完了。このgood cylinder商と通常のhomotopy pushoutによる導来懸垂との比較、
およびF1の指定分解なしの任意モデル源の最終関手が残る。


## S3進捗：通常のhomotopy suspensionと円tensorの対象ごとの同型（2026-10-16）

`General/CircleHomotopySuspension`は実際のgood cylinder商へ一般cone span比較を適用し、
cofibrant EについてQ(0←E→0のhomotopy colimit)≅Q(circle⊙E)を構成する。
任意座標Kで使え、Kの局所化だけで通常の懸垂の可逆性を仮定しない。
利用例は構成済み局所モデルから生成表示・左固有性・実際の作用を取得する。
73宣言・3モジュールの標準公理監査、合同build2902 jobs、幾何的商・導来K逆元・span比較の回帰が成功。
共有一般論`fa1869ce`、適用`90a495e3`。計画§222に記録した。
S3全体は未完了で、この対象ごとの比較の自然性と、ホモトピー圏上の関手同型から
既存の懸垂・ループの導来同値への接続が残る。F1の残項目も維持する。
