# BS-W16 の報告（report-codex-w16.md） — D79 (iii)・M14 の半分・M15 段 0（紙）（§83〜§97、2026-11-13）

元の報告：[report-codex-w16.md](../../bhatt-scholze/reports/report-codex-w16.md)

## 83. M14 の半分の途中報告と D79(iii) の周期係数複体

見込み上端 14,500 行の半分 **7,250 行**を通過した。
(ii) 7,194 行に (iii) の最初の CyclicTateComplex 78 行を加えた時点で **7,272 行**。
停止せず、同じ周期複体の左正則表現での全次数の完全性も検証した。

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| CyclicTateComplex | 78 |
| CyclicTateResolution | 45 |

今回の検証済み追加 **123 行**、(ii)+(iii) の検証済み累計 **7,317 行**。

### 83.1 実測と残りの見込み

| 部品 | §63 の見込み | 現在の実測・残り |
| --- | ---: | --- |
| native Sp の入口と V の全自然比較・局所化 | 3,500〜7,000 | 完成部分 7,194 行。一般係数比較・実現保存は含めない |
| Tate・p 入力・指定類・全自然変換・次数計算 | 3,000〜5,500 | 123 行検証済み。残り暫定 4,500〜8,000 行 |
| 離散・Tot・実現との同じ変換の照合 | 1,000〜2,000 | 未着手、G10 待ち。見込みは据え置き |

現時点の合計見込みは **12,817〜17,317 行**（既検証 7,317 + 残り）。
これは native な Tate 比較を含む暫定値で、完成の保証ではない。
特に Mathlib の `TateCohomology/Basic` は離散な表現の Tate 複体であり、
非有界な p 重テンソルの spectral Tate 関手と、完全加群からの余極限保存延長を
すでに供給するものとして数えない。外枠 **29,000 行**を超える見込みには今はない。
範囲・界面の新しい判断が要る場合は、夜の規則どおり判断点を記して代替の M15 紙へ移る。

### 83.2 証明したもの

`cyclicTateComplexFunctor` は、同じノルムと作用差を交互に用いた整数全次数の
実複体の全関手。全表現射に自然で、二つの微分の合成が零であることを証明した。
群の位数と標数が一致する自明表現では **同じ指定微分そのものが零**。

`cyclicTateComplex_leftRegular_exactAt` は、生成元がある左正則表現の場合に
整数全次数で完全であることを示す。全項の射影性も証明した。
既存の `Rep.FiniteCyclicGroup.leftRegular.range_norm_eq_ker_applyAsHom_sub` と
`range_applyAsHom_sub_eq_ker_norm` を同じ微分へ適用している。
これらは P⁰ の Tate 経路の係数側の部品であり、P⁰ や native Tate 関手の完成ではない。

### 83.3 検証

`cyclic-tate-02.log`・`cyclic-tate-resolution-01.log`：対象ビルド成功、最終版に警告なし。
`audit-cyclic-tate.log`：**127 本・910 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
次は自明表現での指定ホモロジー同型と、その全射に関する自然性を検証する。


## 84. D79(iii)：同じ p 巡回作用・全入力関手・係数類

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| CyclicTateTrivialHomology | 71 |
| TensorPowerRepresentation | 58 |
| CyclicTensorInput | 59 |
| TateCoefficientClass | 49 |

追加 **237 行**、(iii) の検証済み **360 行**、(ii)+(iii) 累計 **7,554 行**。

### 84.1 指定と全自然性

`tensorPowerRepresentationFunctor` は、元のテンソル冪の Koszul 置換作用を
任意の指定置換群を通して制限し、全複体・全鎖写像について表現の複体へ持ち上げる。
`representationCochainComplex`・`representationCochainMap` と
`tensorPower_permutation_naturality` を再利用した。
作用を忘れる指定同型も元のテンソル複体を保つ。

`PowerOperationCyclicGroup p` は宇宙をそろえた Z/p の加法群。
`powerOperationCyclicPermutation` は Fin p 上の同じ左平行移動、
`powerOperationCyclicGenerator` は同じ 1。
群の位数が p であることと、同じ 1 が全元を生成することを証明した。
`powerOperationTensorInput` が要求された p 入力の全関手となる。

`cyclicTateTrivialHomologyNatIso` は自明作用を付けた **全加群関手**についての
整数全次数のホモロジー同型。
`powerOperationTateCoefficientClass` は、同じ指定周期係数複体の H^{-1} における
1 の逆像。値が 1 であることと、非自明係数環なら非零であることを証明した。
この時点では native spectral Tate の類と同定したとは述べない。

### 84.2 検証と次

`cyclic-tate-trivial-02.log`・`tensor-power-representation-01.log`・
`tate-coefficient-class-01.log`：対象ビルド成功。新規四本の最終版に警告なし。
`audit-tate-input.log`：**131 本・970 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
次は同じ完全周期解像度からの Hom 複体と、完全入力での比較を進める。
非有界入力の全次数の積による Hom を、native Tate 関手と無条件に同定しない。


## 85. D79(iii)：完全周期 Hom の指定係数比較と有界な係数の非輪状性

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| LinearHomComplexFunctor | 55 |
| CyclicResolutionHomComplex | 38 |
| CyclicResolutionSingleHom | 57 |
| CyclicResolutionSingleHomology | 51 |
| CyclicResolutionHomNaturality | 89 |
| BoundedAcyclicHomotopy | 63 |
| BoundedAcyclicHomComplex | 51 |

追加 **404 行**、(iii) **764 行**、(ii)+(iii) **7,958 行**。
LinearHomComplexFunctor・BoundedAcyclicHomotopy・BoundedAcyclicHomComplex は
一般の線形／アーベル圏での補助で、基盤への移動候補。

### 85.1 同じ係数類と全自然比較

指定した左正則完全周期解像度から、作用付き入力への実 `linearHomComplex` を取った。
`powerOperationTensorResolutionHom` は元の p 入力との合成の全関手。
自明な離散係数では、同じ Hom 微分そのものが整数全次数で零となる。
`cyclicResolutionSingleDegreeEquiv` は、その各次数を同じ左正則表現の評価で係数へ送る。

`cyclicResolutionDiscreteHomologyNatIso` は、この Hom の H^i と元の係数加群との
**全関手の自然同型**。`cyclicResolutionCoefficientClassIso_value` は
Hom の零次数の 1 に対応する類を、§84 の周期係数模型の負一次の指定類へ送る。
この零次／負一次の違いは、採用した解像度の周期の規約によるものとして明示した。
まだ native spectral Tate と同定したという主張ではない。

### 85.2 係数側の有界性を明示した

`homotopyZero_to_acyclic_boundedAbove` は、各項が射影的な P から、
**上に有界な**非輪状 M への全鎖写像が零にホモトピックであることを示す。
双対の帰納法は Mathlib の `isKInjective_of_injective_aux` をそのまま使い、
非輪状な始域側の零範囲から開始する形で証明した。
`linearHomComplex_acyclic_boundedAbove` は全整数次数の Hom 複体の非輪状性を与える。

周期解像度 P が非有界な係数すべてに対して K 射影的であるとは主張しない。
この補題は完全な入力を bounded 模型で扱う比較の前段であり、
一般入力の Tate と余極限保存延長 T_p を区別する。

### 85.3 検証

`cyclic-resolution-hom-01.log`・`cyclic-resolution-single-homology-01.log`・
`bounded-acyclic-homotopy-02.log`・`bounded-acyclic-hom-complex-02.log`：対象成功。
七本の最終版に新規警告なし。
`audit-cyclic-hom.log`：**138 本・1,042 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
次は p 入力の混合色の巡回軌道の自由性と、完全入力の Tate 比較を進める。


## 86. D79(iii)：混合色の実巡回軌道と誘導周期係数の非輪状性

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| CyclicMixedOrbit | 62 |
| CyclicTensorMixedWords | 50 |
| CyclicTateTensorTrivial | 53 |
| CyclicInducedAcyclic | 51 |
| CyclicResolutionBoundedAcyclic | 29 |

追加 **245 行**、(iii) **1,009 行**、(ii)+(iii) **8,203 行**。

### 86.1 同じ p 入力との接続

`powerOperationCyclicPermutation_mixed_free` は、素数位数の同じ巡回作用について、
非定数な任意の色付けを固定する元が単位だけであることを示す。
`cyclicBinaryTensorWord_fixed` は、これを以前の二色自由比較で使った
**実際の `BinaryTensorWord` と同じ置換作用**に適用する。
軌道写像の単射性と、群から同じ軌道への指定同値も証明した。
これは DAG XIII Proposition 2.2.3 の混合層の自由性の係数側の部分。

`cyclicTateComplex_tensorTrivialIso` は自明係数の右テンソルで
ノルム・作用差の **同じ指定微分そのもの**を保つ複体同型。
`cyclicTateComplex_regularTensor_acyclic` は、平坦な自明係数を付けた左正則周期複体が
全次数で非輪状であることを示す。体上では追加入力の平坦性なしで適用できる。
`cyclicResolutionHom_acyclic_boundedAbove` は §85 の一般補題を同じ指定解像度へ適用した。

native Tate 関手、双加群、P⁰ の全自然変換の完成はまだ宣言しない。
次は上有界係数の準同型を同じ解像度の Hom が保つことを、
同じ cone の全 Hom 比較を通して証明する。

### 86.2 検証

`cyclic-mixed-orbit-02.log`・`cyclic-tensor-mixed-words-02.log`・
`cyclic-coefficient-acyclic-01.log`：対象成功。最終五本に警告なし。
`audit-cyclic-mixed.log`：**143 本・1,065 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。


## 87. D79(iii)：同じ周期 Hom は上有界係数の指定準同型を保つ

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| LinearHomConeDegrees | 46 |
| ModuleConeCoordinates | 75 |
| LinearHomConeComparison | 65 |
| BoundedQuasiIsoCone | 53 |
| BoundedLinearHomQuasiIso | 47 |

追加 **286 行**、(iii) **1,295 行**、(ii)+(iii) **8,489 行**。
前四本および最後の一般補題は、一般の線形・アーベル圏の基盤への移動候補。

### 87.1 指定射の準同型保存

`linearHomConeIso R P f` は

```lean
mappingCone (linearHomComplexPostcompose R P f) ≅
  linearHomComplex R P (mappingCone f)
```

の **実複体同型**。Mathlib の同じ `mappingCone.liftCochain`、
二射影とその直積座標、符号付き微分を照合した。
`coefficientCone_acyclic_of_quasiIso` と逆向きの反映は、
一般のアーベル圏の同じ指定 cone の三角形を通して証明した。

`linearHomComplexPostcompose_quasiIso_boundedAbove` は、P の各項の射影性と
M・N の共通の上界を明示し、**元の指定射 f による後合成そのもの**の準同型性を与える。
`cyclicResolutionHom_quasiIso_boundedAbove` が、同じ指定完全周期解像度への適用。
これで完全入力の係数模型を相対関手として native 側へ運ぶための
準同型保存まで到達した。非有界係数の場合や P⁰ の完成はまだ主張しない。

### 87.2 検証

`linear-hom-cone-degrees-03.log` の Degrees、`linear-hom-cone-comparison-03.log`、
`bounded-linear-hom-quasi-02.log`：対象成功。五本の最終版に新規警告なし。
`audit-bounded-quasi.log`：**148 本・1,103 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
上有界な係数の全部分圏と同じ相対 Hom 関手へまとめる作業を続行する。


## 88. D79(iii)：同じ射影 p 入力の native スペクトル図式と全 sourceIso

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| BoundedCyclicCoefficients | 64 |
| BoundedCyclicSpectrum | 71 |
| TensorPowerHomotopy | 47 |
| TensorPowerUpperBound | 54 |
| TensorPowerRepresentationQuasiIso | 31 |
| BoundedProjectiveTensorInput | 71 |
| ProjectivePowerSpectrum | 65 |

追加 **403 行**、(iii) **1,698 行**、(ii)+(iii) **8,892 行**。
TensorPowerHomotopy・TensorPowerUpperBound の一般補題は基盤への移動候補。
相対図式の各部品も、Tate の実構成が固まった後に配置を検討できる。

### 88.1 到達した実関手

`boundedCyclicHomLocalizer` は、上有界な作用付き係数の元の準同型を保つ
**同じ完全周期 Hom の実相対関手**。
`boundedCyclicSpectrum` は、その hammock から native Sp への実関手であり、
同じ厳密な係数図式へ戻る全 `boundedCyclicSpectrum_sourceIso` を持つ。
上界は対象ごとに選べ、二対象の間の証明で共通の上界を取った。

`tensorPowerMap_quasiIso_of_KProjective` は、指定射を保つホモトピー同値の
同じテンソル冪を使って証明した。作用付き入力の準同型性は正確な忘却で反映した。
上界 n a も同じ符号付き入力に適用している。

`boundedProjectiveTensorInputLocalizer` は、完全入力を含む
上有界・各項射影の元の複体から、同じ巡回係数模型への相対関手。
その p 入力・完全周期 Hom・実スペクトル化の合成が **`projectivePowerSpectrum`**。
`projectivePowerSpectrum_sourceIso` は元の厳密な合成との **全関手の指定同型**。
対象ごとにスペクトルを選ぶ構成で代用していない。

採用した周期のままの未シフト Hom を使っている。
**native Tate[-1] との比較、完全入力からの余極限保存延長、
スペクトル的な右 k 作用、P⁰ の全自然変換はまだ未完了**。
次は同じ係数類を表す実鎖写像と、そのホモロジー類を照合する。

### 88.2 検証

`bounded-cyclic-coefficients-03.log`・`tensor-input-bounds-homotopy-01.log` の
BoundedCyclicSpectrum、`tensor-input-bounds-homotopy-03.log`・
`bounded-projective-tensor-input-01.log`・`projective-power-spectrum-01.log`：対象成功。
新規七本の最終版に警告なし。
`audit-projective-power.log`：**155 本・1,173 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。


## 89. D79(iii)：単位での同じ p 入力と、指定係数類を表す実射

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| CyclicCoefficientSeed | 53 |
| CyclicCoefficientSeedHomology | 55 |
| CyclicTensorUnitComparison | 67 |

追加 **175 行**、(iii) **1,873 行**、(ii)+(iii) **9,067 行**。

### 89.1 同じ単位と指定類の照合

`powerOperationTensorUnitIso` は、元の p 入力の単位での値を、同じ自明な k 係数の
single 複体へ送る実同型。既存 `tensorUnitPower_permutation` と
`tensorUnitPowerIso` を使い、作用の恒等性と同じ縮約を保持した。
`powerOperationUnitResolutionHomIso` により、同じ p 入力と周期 Hom の単位での値が
元の指定係数 Hom 模型へ実複体同型で戻る。

`powerOperationCoefficientSeed` は、その指定係数 Hom へ単位複体から入る **実鎖写像**。
同じ左正則評価で 1 を回収し、`powerOperationCoefficientSeed_homology_value` で
実 H^0 の類も指定比較で 1 に送られることを示した。
`powerOperationCoefficientSeed_matches_class` はその類を、§84 で固定した
同じ周期係数模型の H^{-1} の指定類へ送る等式。
ホモロジー群に任意の射を後から選んだ構成ではない。

native Tate[-1] との比較、同じ境界射の orbit との比較、T_p の延長と
スペクトル的な右 k 作用の照合はまだ必要。
特にこの鎖模型の k 線形な係数種を、未証明の右 k 作用の射として扱わない。
次は同じ周期解像度の正の部分への全自然な制限と、上有界係数の有限支持を進める。

### 89.2 検証

`cyclic-coefficient-seed-02.log`・`cyclic-unit-seed-homology-02.log`：対象成功。
新規三本の最終版に警告なし。
`audit-cyclic-seed.log`：**158 本・1,209 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。


## 90. D79(iii)：同じ周期解像度の正の部分と実スペクトル化

登録候補（`SerrePositivity.EInfinity.PowerOperation.`）：
LinearHomComplexPrecomposition（47 行）、CyclicPeriodicRestriction（56 行）、
RelativeComplexSpectrum（37 行）、CyclicPositiveSpectrum（80 行）。
追加 **220 行**、(iii) **2,093 行**、(ii)+(iii) **9,287 行**。

完全周期解像度の非負次数部分への包含を前合成する、同じ Hom の全自然変換を作った。
上有界係数では次数 n の座標が 0 ≤ i ≤ d−n に限られることも証明した。
正の部分の各項の射影性と、上有界係数の準同型を保つことから、
その実相対関手・native な Sp への関手・厳密な元の図式との全 sourceIso を得た。
RelativeComplexSpectrum は［一般∞］の移動候補。

これはまだ native な orbit との同定や native な Tate 境界ではない。
次は逆生成元の射影解像度によるテンソル余不変の直和全複体と、
同じ正の Hom の有限座標の比較を進める。

対象ビルド `cyclic-positive-spectrum-02.log` 成功、最終版の警告なし。
`audit-cyclic-positive.log`：**162 モジュール・1,242 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。


## 91. D79(iii)：orbit の実解像度・指定評価・有限支持

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| CyclicOrbitModel | 52 |
| CyclicOrbitCoordinateSign | 31 |
| RegularOrbitCoordinates | 68 |
| RegularOrbitNaturality | 62 |
| RegularOrbitDifferential | 55 |
| CyclicPositiveFiniteCoordinates | 79 |
| CyclicOrbitResolutionCoordinates | 52 |
| CofanZeroSupport | 49 |

追加 **448 行**、(iii) **2,541 行**、(ii)+(iii) **9,735 行**。

### 91.1 同じ鎖模型の比較の現在地

逆生成元による Mathlib の実射影解像度を負の余鎖次数へ零延長し、
元のテンソル余不変関手による直和全複体を固定した。
同じ項の同型と同じ指定微分（鎖次数が偶数ならノルム、奇数なら逆生成元の差）を照合した。

Hom 側の左正則評価は係数の元の生成元を使い、
orbit 側の評価は逆元を含む。実余不変射の上でこの差とノルムを証明したので、
逆生成元の選択が同じ係数微分を与えることを確認できる。
係数の全射への自然性も、指定された元の射で証明している。

正の Hom の各次数は、同じ切り詰めの項の同型と左正則評価により
有限な積へ実線形同値で移る。この同値は共通上界を持つ係数射に自然。
直和全複体の符号との比較用に ε_s = (-1)^{binom(s,2)} と隣接次数の比を固定した。
CofanZeroSupport は［一般圏］基盤への移動候補。

**正の Hom と実 orbit 全複体の鎖同型、native orbit/Tate との比較、
T_p の延長、スペクトル的な右 k 作用、P⁰ の全自然変換は未完了**。
いまは零支持を除いた指定余積の同型と、同じ有限対角線の比較を続けている。
現時点で 29,000 行の停止基準を超える見込みはない。

### 91.2 検証

`cyclic-orbit-model-01.log`、`regular-orbit-coordinates-02.log`、
`regular-orbit-naturality-03.log`、`cyclic-orbit-coordinates-01.log`（RegularOrbitDifferential）、
`cyclic-orbit-coordinates-03.log`（CyclicPositiveFiniteCoordinates）、
`cofan-zero-support-01.log`（CyclicOrbitResolutionCoordinates）、
`cofan-zero-support-03.log`：対象成功、最終版の警告なし。
`audit-orbit-coordinates.log`：**170 モジュール・1,307 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。


## 92. D79(iii)：同じ orbit 全複体の有限座標と符号付き次数同型

| 登録候補（`SerrePositivity.EInfinity.PowerOperation.`） | 行数 |
| --- | ---: |
| CoproductZeroSupport | 46 |
| CyclicOrbitDiagonal | 67 |
| CyclicOrbitFiniteSum | 42 |
| CyclicOrbitFiniteCoordinates | 55 |
| CyclicPositiveOrbitDegreeIso | 56 |
| CyclicPositiveDifferentialCoordinates | 86 |

追加 **352 行**、(iii) **2,893 行**、(ii)+(iii) **10,087 行**。

### 92.1 実装した同型と残る可換性

`cyclicOrbitTotalDegreeSupportIso` は元の直和全複体の同じ次数の項に対し、
零の成分を除く指定余積の同型。支持する対角線を 0 ≤ s ≤ d−n に取り直し、
同じ正則余不変の評価を使って有限な積への `cyclicOrbitTotalDegreeCoordinatesIso` を得た。
CoproductZeroSupport は［一般圏］基盤への移動候補。

`cyclicPositiveOrbitDegreeIso` は、正の Hom の有限座標と
ε_s = (-1)^{binom(s,2)} の符号を合成した、**同じ次数の実加群同型**。
微分との可換性を仮定に入れて組み立てたものではなく、
**まだ鎖同型とも native orbit 比較とも主張していない**。

Hom 側では、元の切り詰めの包含の可換性から `cyclicPositiveResolution_inv_d` を示した。
`cyclicPositiveHomCoordinate_delta` は元の Hom 微分の一座標が、
係数微分と (-1)^{n+1} を掛けた同じ周期係数微分との和であるという等式。
次は元の orbit 全複体の指定包含射の座標をそろえ、同じ微分との可換性を閉じる。

### 92.2 検証

`cyclic-orbit-diagonal-02.log`、`cyclic-orbit-finite-coordinates-01.log`、
`cyclic-positive-orbit-degree-02.log`、`cyclic-positive-differential-03.log`：対象成功。
六本の最終版に警告なし。
`audit-orbit-finite.log`：**176 モジュール・1,378 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。夜の規則どおり続行する。


## 93. D79(iii)：元の orbit 包含射の指定座標まで検証

登録候補（`SerrePositivity.EInfinity.PowerOperation.`）：
FiniteBiproductCoordinates（49 行）、CyclicOrbitSummandCoordinates（80 行）。
追加 **129 行**、(iii) **3,022 行**、(ii)+(iii) **10,216 行**。

`cyclicOrbitTotalDegreeCoordinates_inclusion` は、元の直和全複体の
指定包含射を、同じ正則評価・有限双積の指定包含射で表す **元の圏での等式**。
`cyclicOrbitTotalDegreeCoordinates_inclusion_apply` は、その等式を各座標で評価した
Kronecker の式。FiniteBiproductCoordinates は［一般圏］基盤への移動候補。

正の Hom と orbit の **次数同型**は実装済みだが、微分可換性による鎖同型はまだ未完了。
native Tate[-1] の比較・T_p の延長・スペクトル的な右 k 作用・P⁰ の完成も未完了。

`cyclic-orbit-summand-coordinates-02.log`（FiniteBiproductCoordinates）、
`cyclic-orbit-summand-coordinates-06.log`：対象成功、最終版に警告なし。
`audit-orbit-inclusions.log`：**178 モジュール・1,386 宣言、標準三公理のみ**。
sorry・追加公理なし。共有入口・共有監査は未変更。
ここまでの検証済み分をコミットし、夜の停止規則に従い次節の規模確認を記録する。


## 94. 夜の停止規則：M14 の残りの規模を再評価し、Lean を止める

### 94.1 確認できたものと、まだ供給されていないもの

検証済み実装は §93 のコミットまで保存した。実測は (ii) 7,194 行、
(iii) 3,022 行、合計 **10,216 行**（(i) の既存界面・drafts の変更は別）。
(ii) の native Sp の入口と V・π/H は §63.6 の上端 7,000 行にほぼ収まった。
一方、(iii) の当初 3,000〜5,500 行は、現在の **鎖模型の部品だけで 3,022 行**を使い、
以下の三つをまだ含んでいない。§83 の仮置きの残り 4,500〜8,000 行を
引き続き全体の保証として使うことはできないと判断した。

- `projectivePowerSpectrum`・`boundedCyclicSpectrum`・`cyclicPositiveSpectrum` は
  実相対図式から Sp への関手と全 sourceIso を持つが、
  native な homotopy orbit・norm・Tate[-1] との比較ではない。
  KST の `homotopyFixedPoints` とその native limit cone の部品はあるが、
  今の調査ではこの入力で使える native orbit→fixed の norm と指定 Tate 境界の
  全自然比較を発見していない。固定点だけを Tate と呼び替えることはできない。
- `powerOperationCoefficientSeed` の k 線形な実鎖写像と、その指定 H^0 の計算はある。
  これは DAG XIII Construction 2.2.6 の **スペクトル的な右 k 加群の射 e**を
  供給したものではない。新たな右作用とその coherent な照合が必要である。
  `DGKernelBimoduleIso` 等の dg 双加群の比較も、この非 D(k) 線形な作用の代用にはならない。
- p 入力の準同型保存・上界・混合色の自由性は証明したが、
  完全入力上の Tate 構成の exact 性、元の完全 ∞ 圏への全降下、
  余極限保存延長 T_p と指定類の右作用の比較はまだ必要。
  鎖レベルの混合色の自由性だけで、これらの全自然変換を得たとはしない。

### 94.2 重複を除いた残りの暫定見込み

| 残る束 | 追加 Lean の見込み | 範囲 |
| --- | ---: | --- |
| 正の Hom と実 orbit 全複体 | 900〜1,600 | 同じ指定微分の可換性・全自然な鎖同型 |
| native orbit・norm・Tate の比較 | 3,000〜5,500 | 現在の p 入力で使う範囲、指定境界と全関手。右 k 作用は次々行 |
| 完全入力での exact 性・降下・T_p の延長 | 2,800〜4,800 | 同じ p 入力の混合項、完全 ∞ 圏、全自然な余極限保存延長 |
| スペクトル的な双加群と e | 2,800〜5,000 | 右 k 作用・指定係数類・左作用との区別・全比較 |
| BE の作用による P⁰ と Rem 2.2.7 | 1,800〜3,200 | 同じ境界から BE の p 項作用への射と係数計算。Tot は次行 |
| 離散・Tot の最後の照合 | 1,000〜2,000 | G10 後の (iv)。前行との二重計上なし |
| **残り** | **12,300〜22,100** | |
| **既知実測と合わせた全体** | **22,516〜32,316** | (i) の小さい変更は別 |

これは未証明の部分の工程見込みであり、数学的な不可能性や下界の主張ではない。
ただし現時点で上端を **29,000 行**以内にする、既存宣言による検証済みの短縮経路はない。
当初の「P⁰ の Tate・指定類・全自然変換」の一行の中に、
鎖模型→native の境界、exact な延長、スペクトル的な右作用という別の未供給の束が残る。
これらを表の外へ出して行数から除くこともしない。

したがって coordination.md §2「夜の進め方」の **上限を超えそうな場合**として、
**M14 の Lean はここで止め、M15 の一般 R 加群の段 0 の紙の作業へ移る**。
上限の引き上げや界面の追加は自己承認しない。朝の判断点は、
上の native Tate・スペクトル的な module の供給と分担、および M14 の範囲の切り方。
G10 の有無だけを、現在の鎖同型の未完了の理由にしてはいない。
承認を求めて今夜の作業を止めず、次節へ進む。


## 95. 代わりの作業：M15 の一般 R 加群、§66 の続き（紙のみ）

### 95.1 今夜の実装から再利用できるもの

`eilenbergMacLaneDerived A` は一般の可換係数環 A の既存 D(A) から
native Sp への実関手であり、`eilenbergMacLaneDerived_homologyIso A i` は
その全ホモトピー圏の π/H 比較。M15 で台をスペクトルとして読むときは再利用できる。
一般の E∞ 頂点 R 上の加群をこれで構成したことにはならない。
係数制限と V の全比較も未供給のままである。

§66 の左加群の通常圏の部品に加え、次の **既存の native dg module** の出力を
最初の模型の束で再利用する候補として確認した。

| 既存宣言 | 実際に供給するもの | M15 へ接続する前に要るもの |
| --- | --- | --- |
| `dgAlgebraDerivedInfinityCategory A B` | B : Mon (Complex A) 上の右半自由 dg 加群の実 ∞ 圏 | BE の厳密代数から同じ dg 代数を作る全関手と、一般 R への降下 |
| `dgAlgebraDerivedInfinityCategory_isStable` | 同じ dg 代数上の module ∞ 圏の安定性 | E∞ 頂点 R に対する module 圏との比較 |
| `dgModuleHomSpaceInfinity`・`dgModuleHomSpaceValueEquivalence` | 両変数で coherent な空間値 Hom と同じ Hom end の比較 | R 加群の RHom、相対テンソルとその随伴の比較 |
| `dgModuleExtensionYonedaNerveIso` | 既存 dg 圏の拡大と同じ Yoneda に対する指定比較 | BE の係数射と、同じ単位加群・指定辺への適用 |
| `dgKernelTensorIsoNerveOfBimoduleIso`・`dgKernelDerivedInfinity_bimoduleIso` | 実 dg 双加群同型による kernel 関手の比較 | E∞ の相対テンソルと対称性の整合 |
| `dgBimoduleFunctorHomFunctor_resolvedMap_isIso_of_quasiIso` | 指定した dg 双加群の解決済み射の同型性 | 必要な BE 加群の双加群を実際に供給すること |

`dgAlgebraDerivedInfinityCategory` は一般の非可換 dg 代数を受け取る。
ここで H^0(R) に落とす必要はない。ただし、それだけでは
E∞ の相対テンソルの対称性は供給されない。

### 95.2 最初に検査すべき型と射の範囲

以下は **未実装・未型検査の型案**。本体・界面・drafts の宣言の追加ではない。
`Complex`・BE の operad の名前空間を開いた文脈で記す。

```lean
-- 厳密 BE 代数の同じ台と、指定した単位・積を持つ dg 代数。
barrattEcclesAssociativeForget (A : Type u) [CommRing A] :
  (operad A).Algebra ⥤ Mon (Complex A)

-- 上の関手が構成できた後の、厳密な各入力での候補。
strictModuleInfinity (X : (operad A).Algebra) : SSet.{u+1} :=
  dgAlgebraDerivedInfinityCategory A
    ((barrattEcclesAssociativeForget A).obj X)

-- 同じ唯一の対象で評価して台へ戻す、全射を含む候補。
strictModuleUnderlying (X : (operad A).Algebra) :
  strictModuleInfinity X ⟶ derivedInfinityCategory A
```

最初の検査は、BE の指定零単体の操作から strict な単位・積・結合性が
元の複体で成立することと、全代数射がそれを保つこと。
`homologyCommRing` の供給だけではこの型を満たさない。
この検査が閉じたら、一対象 dg 圏の既存の実 module 構成を適用できる。
閉じない場合の enveloping algebra の経路は別の設計判断であり、ここで採用しない。

一般の native 頂点 R に対する型は §66.1 の `modulesOver`・`moduleUnit`・
`algebraAsModule`・`moduleExtend`・`moduleRestrict` のまま。
これへ進むときは次を同じ指定射で照合する。

1. 厳密 BE の準同型に対する restriction と extension の随伴。
2. BE の弱同値に対する module ∞ 圏の同値と、台の忘却との全比較。
3. native な CAlg の射と合成に対する module 圏の降下。
   頂点ごとに厳密模型を一つ選んで終わりにしない。
4. E∞ の高次の可換性を使った相対テンソルの対称性・結合性・単位。
5. 単位から `algebraAsModule f` への指定辺、その fiber、n 重テンソルの指数射。

### 95.3 地図との対応と見込み

`research/ha-coverage/review/ch4.csv` の記載を再確認した。
4.2.1.15 は通常の `Mon`・`Mod`、4.2.3.5 は通常の内部加群の余極限、
4.5.2.1 は通常の balanced tensor の特殊例という部分一致であり、
4.5.3.1 の変わる代数に関する全 module の射影は未供給という判定。
この地図は native な一般 R の module の既証明性を意味しない。

§66.4 の **2,500〜4,500 行**は、以下の再利用を前提とする暫定見込みとして保持する。
既存の dg module の安定性や Hom 空間を新しく作り直す費用は加算しない。

| 束 | 追加の暫定見込み | 停止前に供給すべき指定比較 |
| --- | ---: | --- |
| 厳密 BE と既存 dg module、native な係数射への降下 | 700〜1,400 | 台・単位・全 restriction/extension・弱同値不変性 |
| E∞ の相対テンソルと底変換 | 1,200〜2,200 | 対称性・結合性・単位、同じ pushout の辺 |
| fiber・thick ideal の利用側への接続 | 600〜900 | 同じ単位と指定辺、テンソルによる有限余極限保存 |
| **計** | **2,500〜4,500** | |

RHom・完備版・Amitsur の Tot の利用側は §66.3 の後続であり、この模型の束と二重計上しない。
M15 に入るときの担当決定では、上の一般 R の module と相対テンソルの供給者を
先に確定する必要がある。M14 の **スペクトル的な右 k 作用**と、
ここでの **R 加群の相対テンソル**には別の比較が要るため、
一方が終われば他方も終わるという見込みは置かない。

この節は紙のみ。M15 の Lean・新たな界面・drafts の型変更には着手していない。
今夜の代わりの作業の段 0 として報告する。


## 96. M14 の範囲の比較・段 0（11-13、§25、紙のみ）

基準は本枝 `e33d5dc1f`。main の指示書 §25 も `git show main:...` で読んだ。
**界面・drafts・Lean は変更していない。ビルド・監査・整理券の取得もしていない。**
以下は設計の判断材料であり、D79 の改訂を実施・自己承認したものではない。

### 96.1 結論と二つの範囲

**BS の Lemma 8.4 の結論には、π_n 上の加法的演算と、CAlg の射への自然性で足りる。**
ただし、現在の五つの欄を成分の型へ機械的に置き換えるだけでは、
現 drafts の証明の筋を全部閉じたことにはならない。
**levelwise Frobenius と、単体的余単体的模型の実現上の演算との比較が別に必要**。
特に π_n は一般の幾何学的実現の各段の π_n の余極限ではない。
filtered 余極限についての議論を、単体的実現へそのまま適用しない。

| 範囲 | BS で受け取る出力 | 残る中心的な比較 | 見込み |
| --- | --- | --- | --- |
| 今の D79、coherent Sp 値の演算 | 実スペクトルの自己変換と π_n の計算 | native Tate・右 k 作用・T_p・指定境界、実現の比較 | §94 の全体 22,516〜32,316 行。上端は基準超過 |
| May の成分の演算 | ho(CAlg F_p) 上の可換群値関手の自己自然変換 | 正規化した May 演算、同じ BE の Tot・実現模型の Frobenius 計算 | 新規 5,500〜9,950 行。後述の模型比較を含む暫定見込み |

May 案なら、native な orbit・norm・Tate、スペクトル的な右 k 加群の e は
この BS の証明に不要となる。May の **代数的な巡回解像度 W** と
`W ⊗_{C_p} X^{⊗p}` は使う。これを native な homotopy orbit の構成と混同しない。
coherent な Sp 値の演算との一致は、新しい BS 界面を埋める前提にはせず補完へ回す案。

### 96.2 利用者の全確認

`powerOp0` と `powerOperationZero*` を本体・drafts 全体で検索した。
直接の消費者は Shared/EInfinityPowerOperation、組み立て関数 Assembly、
Shared/BarrattEcclesTheory の供給欄。A4 の証明本体はまだ sorry と証明方針である。
したがって、以下の「足りる」は **証明に必要なデータの確認**であり、
未実装の A4 の証明を検証したという意味ではない。

| 宣言・箇所 | 現在要求するもの | 成分の演算での扱い |
| --- | --- | --- |
| A4 `prismaticPerfection_coconnective`（277 行以降） | mod p の shift と P⁰ の一致、可逆性、正の π の消滅 | 各 π_n の演算の等式と自然性でよい。filtered 塔の π の比較と、下記の模型の実現比較が必要 |
| A4 `prismaticPerfection_h0_perfectDelta` | H⁰ mod p の Frobenius、C/p の単射、shift の可逆性 | π_0 の等式でよい。P⁰ の高次 coherent 性は使わない。p 完備性・δ 構造は別の既存の工程 |
| Shared `homotopy`・`homotopyCohomology`・`homotopyMap` | H^{-n} と π_0 の環の読み替え | そのままの加法群で利用可能 |
| `powerOperationZero`・`_zero`・`_pos`・`_natural` | 演算の成分、零次、正次数、各辺への自然性 | 弱い型で供給できる |
| `powerOperationZero_natTrans`・`_primeField` | **FunctorHom 自体** | 現在の型は弱いデータからは作れない。BS 側は通常の NatTrans へ書き換える案。元の強い出力は補完側 |
| `powerOperationZero_component` | 実 Sp の成分を π に送った等式 | 現在の等式は弱いデータからは作れない。BS には H^{-n} の成分を読む等式だけを残す案 |
| `powerOperationZero_eq_frobenius_discrete` | ho(Sp) の射の等式 | 全 n の可換群準同型の等式へ弱めればよい |
| `powerOperationZero_eq_frobenius_tot` | ho(Sp) の射の等式、コメントには実現への移行も含む | 全 n の準同型の等式へ弱められるが、証明には May の Tot 模型での直接計算が要る |
| Shared の末尾 172–177 行の証明方針 | coherent な自然変換と極限・実現の比較 | **ここが現在の高次の整合を使う方針**。弱い型ではそのまま使えない |

上の三つの強い補助出力を外部で消費する Lean の呼出しは検索で見つからなかった。
A4 冒頭の coherent という説明も、決定後に成分の説明へ直す対象。
A3/DiscreteCase の G-A3-9 には Shared から π_0 の部分を前倒しする方針の参照がある。
これも π_0 の比較で足りるが、⑤c のファイルなので今回は変更しない。

**filtered の段**：演算を全対象に定義して辺に自然にしておけば、
各余極限の脚との自然性と、π_n と filtered 余極限の比較から、
余極限上の演算は各段の演算の余極限に一致する。
可逆な shift と一致して正の π_n では零なら、その群は零となる。
これには `forget_preservesSifted` の filtered の部分等の供給は要るが、
P⁰ の Sp 値の coherent な持ち上げは要らない。
完備化については π と任意の完備化の可換性を新たに仮定せず、
従来の p 完備性・導来 Nakayama・t 構造の工程を使う。

### 96.3 新しい型の案

最小案は **F_p に限った本欄**とし、π_n を H^{-n} の台の加法群として読む。
以下は未型検査の Lean の型案。既存 `hoMap`・`additiveCohomologyOnHo` を用い、
`E` の欄の記法を省略して `CAlg`・`forget`・`pi0`・`pi0_forget` を書く。
`ν B` は既存 `nerveVertex B` の略記。

```lean
-- 界面の補助。C と U を引数にすれば E の定義中にも循環せず使える。
abbrev homotopyGroupsOnHo (k : Type u) [CommRing k]
    {C : SSet.{u+1}} (U : C ⟶ derivedInfinityCategory k) (n : ℤ) :=
  hoMap U ⋙ additiveCohomologyOnHo k (-n)

-- 以下 Π p n := homotopyGroupsOnHo (ZMod p) (forget (ZMod p)) n。
powerOp0 (p : ℕ) [Fact p.Prime] (n : ℤ) :
  Π p n ⟶ Π p n

powerOp0_zero (p : ℕ) [Fact p.Prime]
    (x : (CAlg (ZMod p)) _⦋0⦌)
    (a : ((pi0 (ZMod p)).obj (SSet.HomotopyCategory.mk x)).right) :
  let e := (pi0_forget (ZMod p)).app (SSet.HomotopyCategory.mk x)
  (powerOp0 p 0).app (SSet.HomotopyCategory.mk x) (e.hom a) = e.hom (a ^ p)

powerOp0_pos (p : ℕ) [Fact p.Prime]
    (x : (CAlg (ZMod p)) _⦋0⦌) (n : ℤ) (hn : 0 < n) :
  (powerOp0 p n).app (SSet.HomotopyCategory.mk x) = 0
```

`powerOp0 p n` は **通常の可換群値関手の NatTrans**。
`FunctorHom` ではない。CAlg の全ホモトピー圏の射で自然性を述べるので、
辺をホモトピーで取り替えた不変性・恒等射・合成もこの型に含まれる。
各 `SSet.Edge` への自然性は `SSet.HomotopyCategory.homMk f` で評価すれば得られる。
辺ごとの等式だけを別々に欄にするより、局所化と照合しやすい。
Sp の π で表記する案も `toSpectra_homologyIso` で共役すれば同じ強さになるが、
この H^{-n} の案では P⁰ のための V や係数制限の V の比較を必要としない。
既存の `toSpectra*` 欄を削除する提案・変更は今回は行わない。

F_p 上では Frobenius は F_p を固定するので、離散 Frobenius は
B → Res_{Frob} B の代わりに **B → B の F_p 代数の射**として書ける。
これにより不要な係数制限の同型を型から外せる。

```lean
powerOp0_discrete (p : ℕ) [Fact p.Prime]
    (B : RingAlgebra (ZMod p)) (f : B ⟶ B)
    (hf : ∀ a : B.right, f.right.hom a = a ^ p) (n : ℤ) :
  let x := atVertex (discrete (ZMod p)) (ν B)
  (powerOp0 p n).app (SSet.HomotopyCategory.mk x) =
    (Π p n).map (SSet.HomotopyCategory.homMk
      ((nerve.edgeMk f).map (discrete (ZMod p))))

powerOp0_tot (p : ℕ) [Fact p.Prime]
    (X : CosimplicialRingAlgebra (ZMod p)) (f : X ⟶ X)
    (hf : ∀ j (a : (X.obj j).right), (f.app j).right.hom a = a ^ p)
    (n : ℤ) :
  let x := atVertex (ofCosimplicial (ZMod p)) (ν X)
  (powerOp0 p n).app (SSet.HomotopyCategory.mk x) =
    (Π p n).map (SSet.HomotopyCategory.homMk
      ((nerve.edgeMk f).map (ofCosimplicial (ZMod p))))
```

いずれも **全整数 n の可換群準同型の等式**。n=0 だけへは弱めない。
一般の `[CharP k p]` での Shared の API を残すなら、F_p → k に沿う CAlg の制限と
`restrict_forget`・`restrictD_homologyIso` から
`Π_k(n) ≅ hoMap(Res) ⋙ Π_{F_p}(n)` を作り、その自然同型で上の演算を共役する。
この一般 k の補助は自然性を運ぶだけで、新たな Sp 値の持ち上げは要らない。
一般 k の `_discrete`・`_tot` は係数制限と同じ模型の比較も運ぶ必要がある。
F_p の本欄を供給することと、全 k に対する欄を別々に新規証明することを混ぜない。

### 96.4 May の構成と局所化までの不足

原典を確認した箇所：
[May, Definitions 1.2・2.1・2.2, Proposition 2.3](https://www.math.uchicago.edu/~may/PAPERS/10.pdf#page=8)、
[より明示的な May–Steenrod の定義、§5・Definitions 8–10](https://arxiv.org/pdf/2010.02571#page=9)。
BE からの作用の出典は [Berger–Fresse](https://arxiv.org/pdf/math/0109158)。
ここで用いる原典の範囲は、巡回解像度からの演算の定義・加法性・自然性と、
その零次の値。Adem 関係・全 Cartan 公式・全ての冪作用を実装する必要はない。

homological な n（本体の H^{-n}）で、W の i 番目の生成元を e_i とし、
同じ BE 作用から D_i[a] を作る。May の正規化を採れば、P⁰ は
p=2 で D_{-n}、奇素数で ν(n)D_{-n(p−1)}。負の添字の D_i は零とする。
したがって n>0 の消滅は添字から、n=0 の値は D_0 の積から得られる。
ν(n) は May の整数次数の符号・階乗の単元であり、負の次数での逆元も含む。
係数を勝手に 1 としない。巡回生成元・Koszul 符号・ν を最初に同じ規約にそろえる。

必要な実装を次の順で切る。

1. **W → E(p)**：非負の巡回射影解像度を、制限した BE の arity p の増大解像度へ写す。
   e_0 の増大は 1 とし、同変な鎖比較を固定する。
   `augmentation_quasiIso`・`complexAugmentation_quasiIso`、左正則の射影性、
   Mathlib の射影解像度の比較・ホモトピーの部品を再利用できる。
   ただし必要な同変比較そのものは未供給。対象ごとに非自然な BE 作用を選ばない。
2. **代表元の独立性・加法性**：θ(e_i ⊗ a^{⊗p}) が cycle となり、
   境界による a の取り替えで同じ類になること、混合項が境界になることを示す。
   固定した θ を全厳密代数で使い、演算を加法準同型として得る。
   `CyclicMixedOrbit`・`CyclicTensorMixedWords` はこの混合項の自由性に再利用できる。
   混合語の自由性だけでは、境界の原像の構成と代表元独立性まで済んではいない。
3. **全厳密 BE 射への自然性**：作用保存から homologyMap と演算の可換性を示す。
   全次数の `homologyFunctor` と `Operad.Algebra.forget` を使える。
   既存 `HomologyAlgebraFunctor` の H⁰ の自然性は実装の手本。
4. **擬同型不変性**：厳密 BE 射 f が擬同型なら H^{-n}(f) は同型。
   3 の可換式を同型で共役すれば、操作を両側で同定できる。
   これに任意の複体への tensor 冪の準同型保存を新たな仮定として加える必要はない。
5. **CAlg の全辺への降下**：`ordinaryAlgebraHoSource_isLocalization` が既存。
   H^{-n} の関手を通常の局所化へ降ろし、Mathlib
   `Localization.liftNatTrans`・`liftNatTrans_app` で操作を降ろす。
   `barrattEcclesPi0`・`barrattEcclesPi0_sourceIso` と同じ局所化を使い、
   既存の忘却先の H^{-n} 関手との自然同型で共役する。
   これで arbitrary な CAlg の辺にも自然となり、coherent Sp 値の変換の局所化は不要。
   残る新規部分は、その全次数の sourceIso と共役・成分の照合。

`powerOperationCoefficientSeed`・`powerOperationCoefficientSeed_homology_value` は、
今夜固定した **完全周期 Hom の単位係数類**の値 1 の検証として再利用できる。
ただし May の W → E(p) の全高次数の比較を供給する宣言ではない。
May の e_0 の規約へ運ぶ比較を明記して使い、既存の H⁰=1 だけから
ν や Tot 上の P⁰ の値を決めない。
`CyclicOrbitProjectiveResolution` は逆生成元で固定されているため、
May の巡回群の同定を合わせるか、元の生成元を引数にした Mathlib の W を使う。
ここは最初の紙・型の区切りで点検し、既存の公開定義を改変して規約を吸収しない。

### 96.5 `_discrete`・`_tot`・A4 の実現比較と G10

**離散**：n=0 は上の D_0 の積、n≠0 は離散代数の H^{-n}=0 で閉じる。
`discrete_forget` と `strictToD_homologyIso` を介する。G10 の待ちは不要。

**cosimplicial な `_tot`**：正規化（または比較射を保持した交代余面）複体の
同じ BE 作用について、正規化した May の top operation が
各 cosimplicial degree の a ↦ a^p を誘導することを直接計算する。
通常の p 重 cup 積は次数を変えるので、この証明として使わない。
n>0 は Tot の coconnectivity、n=0 は零次、**n<0 はこの top operation の計算が核心**。
離散入力上の等式と各射影への自然性だけでは n<0 の等式は得られない。

既存の `TableReduction`、Surjection の実対称列・operad、IntervalCuts の演算、
Alexander–Whitney の構成は部品として再利用できる。
ただし現在の `IntervalCuts.cochainAction` は区間上の構成であり、
任意の余単体的可換環上の top operation の計算済み API とは数えない。
BF のコチェイン作用と、`ofCosimplicial` の **同じ CAlg 対象**の比較が必要。
下の複体の擬同型だけでその BE の冪作用の一致を結論しない。

- 厳密なコチェイン模型での May/Frobenius の計算は G10 なしで進められる。
- 指定された native Tot とその Frobenius 辺へ運ぶ段は、同じ BE 図式・錐と
  実現を比べる G10／③-b の比較を要する。単に成分の型に変えただけでは、この依存は消えない。
- `ofCosimplicial_forget`・`strictToD_homologyIso` の欄を仮定した利用側は、
  その比較を使って H^{-n} 上で読むだけでよいが、BE 実例で欄を供給する工程は別に残る。

**単体的余単体的模型**：BS の [Lemma 8.4 の証明](https://people.mpim-bonn.mpg.de/scholze/prisms.pdf#page=63)
はこの模型の実現上での levelwise Frobenius の一致を使う。
Shared の現在の `_tot` の型が取るのは cosimplicial X **一つだけ**であり、
その文面だけでは外側の単体的実現の比較を供給していない。
現在の「coherent なので実現へ移る」というコメントを、新しい弱い界面の証明に流用できない。

ここは次の **追加の証明義務**として明示して決める必要がある。

- 厳密な simplicial-cosimplicial F_p 代数 X の、指定 BE 実現模型 Y と、
  levelwise Frobenius の誘導する指定辺 F_Y : Y → Y に対し、
  **全整数 n で** `(powerOp0 p n).app (mk Y) = (Π p n).map (homMk F_Y)`。
- 行数には、double complex の同じ BE 作用と正規化・実現の比較を含める。
  π を levelwise に取り、その余極限と書き換えて証明済みにしない。
- これは A4-local な模型比較補題として置くか、`_tot` を二重模型まで含む欄へ広げるかの判断点。
  前者なら五欄の改訂に留められるが、その補題の証明は M14 の BS 用の範囲に含める必要がある。
  **その証明を範囲から外したまま「五欄だけで A4 全体が閉じる」とは報告しない。**

May の鎖操作でこの比較を直接作る経路は紙の上では取れる。
原典の BS の比較主張と整合するが、該当する現モデルの Lean 証明は未供給。
この段では G10／③-b の「同じ厳密模型・指定射・native 実現」の比較を利用する。
filtered な Frobenius 塔へ移る最後の段は 96.2 の辺への自然性で足りる。

### 96.6 再利用の行数と新規見込み

今の **10,216 行**を削除・改変する案ではない。May 経路の必須の新規量からは、
使わない Sp/Tate の構成を外し、既存の完成分としては別に残す。

| 既存分 | 実測 | May 案での位置 |
| --- | ---: | --- |
| D79(ii) の V・π/H とその基盤 | 7,194 | H^{-n} に直接値を取る最小案では必須でない。Sp 表記の共役や補完にはそのまま使える |
| TensorPowerRepresentation・CyclicTensorInput | 117 | p 入力と同じ巡回作用を直接再利用 |
| CyclicMixedOrbit・CyclicTensorMixedWords | 112 | 加法性の混合語の自由性を直接再利用。境界計算は追加 |
| CyclicTensorUnitComparison | 67 | 同じ単位入力の比較を再利用 |
| CyclicOrbitModel | 52 | 代数的な W と全複体の部品。逆生成元の規約を点検した上で一部を使う候補 |
| CyclicCoefficientSeed・CyclicCoefficientSeedHomology | 108 | 単位係数の規約照合の参考・再利用候補。May の全操作を既に供給したとは数えない |
| その他の D79(iii) | 2,566 | 主に周期 Hom・native 図式・有界比較・orbit 座標等。May の最小経路には要求しない |
| **計** | **10,216** | 直接の共通部分 296 行、さらに 160 行が条件付き・規約照合の候補 |

| 新規の束 | 暫定見込み（行） | 完了と数える出力 |
| --- | ---: | --- |
| May の W→BE、cycle・境界・加法性・自然性、ν の規約 | 2,000〜3,500 | 任意次数の厳密 BE ホモロジー上の演算 |
| ho(CAlg) への局所化と全 H^{-n} との比較 | 350〜650 | 全辺に自然な NatTrans |
| 界面・Assembly・Shared/A4 の型の移行 | 250〜450 | 承認された範囲だけの五欄と補助 |
| 離散入力 | 100〜200 | 全 n の `_discrete` |
| cosimplicial 模型の top operation と `_tot` | 1,000〜1,800 | 同じ作用・同じ Frobenius 辺の比較 |
| simplicial-cosimplicial の実現上の比較 | 1,500〜2,800 | 上記の A4 に必要な追加証明義務 |
| filtered 塔と A4 の利用側の成分の照合 | 300〜550 | shift と P⁰、正の π と π_0 の利用 |
| **新規計** | **5,500〜9,950** | |

全既存分を残しても **15,716〜20,166 行**という暫定見込みになり、
元の停止基準 29,000 行は上げない。③-b の一般の G10 の新規実装費を本レーンへ二重計上しないが、
本レーンの BE の模型への適用・指定射の照合は上の Tot・実現の行に含めた。
単に `_tot` の型を弱めて証明済みとする見込みではない。

実装の承認が出た場合の最初の区切りは、W→BE の型・巡回生成元・ν・D_0 の値まで。
その後は代表元独立性と加法性、局所化、Tot、外側の実現の順。
新しい範囲の段ごとの停止基準は、調整役が範囲を決めるときに設定する対象であり、
この表を自己承認の新たな枠として Lean を再開しない。

### 96.7 今回の判断点

成分の May 案を選ぶなら、(1) F_p の本欄＋一般 k は制限で読む補助、
(2) ho(CAlg) 上の可換群値 NatTrans、(3) coherent Sp 値の三つの補助出力は補完、
(4) A4 に必要な二重模型の実現比較を同じ BS 用の範囲へ含める、という切り方が候補。
新しい界面の変更も、May の Lean も今回は実施しない。
**この段 0 の紙の確認はここまで。承認を先取りせず、M15 の段 0 の続きへ進む。**


## 97. M15 の段 0 の続き：BE から dg 代数への最初の接続（紙のみ）

§95.2 の最初の検査を、今回の原典と現ソースの確認でさらに切り分けた。
[Berger–Fresse の冒頭の filtration の説明](https://arxiv.org/pdf/math/0109158#page=2)
では F₁E が結合的 operad である。この部分を使えば、
BE を可換 dg 代数と同一視せずに、通常の **結合的 dg 代数**への忘却を作る経路がある。
この源は現 BE 模型の内部の操作であり、BS のために一般の ∞-operad を新設する案ではない。

ただし現在の `homologyBinary` は `aritySection`（収縮の切断）から作られ、
`homologyBinaryAssociativityHomotopy` は二つの括弧付けの **ホモトピー**を供給する。
この宣言だけを `Mon (Complex A)` の厳密な結合則として使うことはできない。
標準の零単体の係数を使うか、選んだ切断がその係数に一致することを先に証明する。

最初の新規候補の型は次のとおり（紙の型案、未実装・未型検査）。
既存 `coefficientComposite` の添字 m,n,i と同じ規約を用いる。

```lean
standardCoefficient (A : Type u) [CommRing A] (n : ℕ) :
  𝟙_ (Complex A) ⟶ (operad A).arity n

standardCoefficient_unit :
  standardCoefficient A 1 = (operad A).unit

standardCoefficient_composite (m n : ℕ) (i : Fin (m + 1)) :
  coefficientComposite m n i
    (standardCoefficient A (m + 1)) (standardCoefficient A n) =
  standardCoefficient A (m + n)

barrattEcclesAssociativeForget (A : Type u) [CommRing A] :
  (operad A).Algebra ⥤ Mon (Complex A)
```

前二つの等式には零 arity の挿入を含める。これにより、同じ代数の作用へ入力した
μ と η の単位・結合則を **元の複体で**示し、全 BE 射の保存を束ねる。
`aritySection_augmentation`・`coefficientHomotopy` は既存の H⁰ の積との比較には使えるが、
標準係数の厳密な合成の等式をホモトピーだけで代用しない。

この接続ができた後は §95 の既存
`dgAlgebraDerivedInfinityCategory A B`・`dgAlgebraDerivedInfinityCategory_isStable`
を適用する。既存の模型は **右加群**なので、最初からその向きを明記する。
E∞ の高次の可換性から相対テンソルの左右の作用と対称性を供給する工程は、
結合的な忘却だけでは閉じない。

担当を決めるときに最初に受け渡すべき出力は、固定した X での圏だけでなく、
以下を同じ台の忘却と単位について保持したもの。

1. 全厳密 BE 射 f に対する dg 代数射と module の restriction/extension。
2. f が BE の弱同値のときの module ∞ 圏の同値と、同じ単位・台の比較。
3. native CAlg の全辺と合成への降下。
4. 一般の E∞ 頂点 R の相対テンソル、単位・結合性・対称性、および底変換。

1–3 を先の供給者、4 を利用側が別に作る分担も可能だが、
引数の型と同じ指定射を共有しないまま固定 R ごとの圏だけを受け取る形にはしない。
これは §95 の模型と相対テンソルの束の詳細化であり、見込みの行数へ追加加算しない。
一般 R 加群の 2,500〜4,500 行は、既存 dg module の再利用を前提にした暫定値のまま。
M15 の実装担当・界面・相対テンソルの供給者について、今回決定や変更はしていない。

**本ターンの変更は報告 §96〜97 のみ。M14 の Lean の停止は維持し、
M15 も段 0 の紙まで。** 型・範囲の判断を先取りする Lean の下書きも作っていない。

