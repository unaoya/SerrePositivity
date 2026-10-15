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
