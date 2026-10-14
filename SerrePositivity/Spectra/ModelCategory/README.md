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
