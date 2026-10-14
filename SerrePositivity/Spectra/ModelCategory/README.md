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
