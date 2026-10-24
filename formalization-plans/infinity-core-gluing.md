# D2 レーン：β4 dg gluing = 安定 ∞ 圏の lax pullback

> **v3（2026-10-24）**：D2 レーンの正本。所有：`Derived/Gluing/`。完了後は D に吸収。
> foundations.md §2 の β4・§6 の D2。dg 側は D の β5・β3、lax pullback は `F2/CatInfinity/` を読み取り専用で使う。
> 用途は K の Tamme・Land–Tamme の対象供給と、⊙ の Verdier 商の dg 側の同定。

## 引き継ぎ（2026-10-24）

### 現在地
- (a)〜(c) 完了。比較差は `gμ − νf`。実 Hom は同じ mapping cocone、全次数の単位・合成・微分を保持する。
- native dg 圏・左右射影・comma 比較、実円錐・全整数シフトと dg 自然な Yoneda 加群比較を構成済み。
  `dgGluing_isDGPretriangulated` は元 C・D の前三角性を明示入力とする。
- 因子 dg 準同値・順序 ⟨D,C⟩ の半直交性、H⁰ の実随伴・完全忠実な切断、K(Gluing) の実分解三角形を供給済み。
  元 H⁰ の未導入の三角構造や ∞ 随伴を結論していない。
- 一般対象宇宙の比較は対象・Hom を変えず、nerve の単体だけを共通宇宙へ ULift。二射影と augmentation の全 prism を保持する。
- (d) の本質的全射性は証明済み。充満忠実性は正本 `dgGluingLaxHomPullbackComparison` の実ホモトピー同値性に帰着済み。
  入力側の二脚は元の左右 Hom 鎖射影に一致。係数側の入力付き path 比較は同値。正本との全 path 比較は未完。
- 二端点 path 複体の厳密引き戻し・Kan 射影・極限錐、通常区間族への同値、β5 の実半自由分解による canonical 係数比較を構成済み。
- 正本の矢印 Hom を同じ共通対角を持つ二合成対応へ移送済み。元 augmentation・全二三角形・元 Hom 入力を回収する。
- native 前後 cube・共有面・元 augmentation 面と F2 の実二三角形・正規化 cochain 面を全パラメーターで照合済み。
  元負 primitive の明示 prism、係数の宇宙変更、pinched→区間評価を保持する。
- Yoneda 空間同型の実逆射と canonical 始域同型の逆を照合済み。前の未追跡2ファイルは接続・監査済み。
- 実後 cube の区間面を canonical 導来係数の同じ区間評価へ厳密照合し、主係数 path との両端固定ホモトピーを供給済み。
- 左右入力 fiber 内の変形と選択済み変形の二端・基底固定の二次元比較を供給済み（実変形を入力とする補題）。
  cube の全時間三角形族は元端で正本の二三角形、共有端で後 cube、正規化端で canonical 係数面を回収する。
- 共有面に沿う実 cube の pushout 貼り合わせ、標準合成三角形上の全 augmentation prism と三面を構成済み。
  前後の標準合成三角形と元 Hom の終側合成を、全入力の四面体の三つの指定面として保持する。
  同じ実導来 augmentation 四面体の二面は native 前後 prism に厳密一致する。
  四面体全体の二射影間の実ホモトピーと四面すべての制限を保持する。native 実導来 augmentation でも四面を回収する。
  入力固定二変形の関手圏の類の一致、および類の合成等式から指定三辺の境界充填への移送を供給済み。
  実入力二変形の三角形と全時間の射影一致があれば、選択済み対角三辺の指定境界へ移す接続も供給済み。
  augmentation 全四面体を四つの四単体族へ制限し、隣接片の共有三面と両端の二射影四面体を厳密に回収する。
  固定二辺を全時間で保つ補正済み三角形族から合成対応内の実ホモトピーを作り、元入力付き引き戻しへ持ち上げる入口も供給済み。
  六つの側面射影等式は coherent prism の自然性から Small 仮定なしで実例化済み。
  標準正規化閉射の augmentation 対角は元 augmentation の実一単体に一致し、閉零元での augmentation primitive の零性も回収済み。
  標準正規化の両側面で、二つの生成三角形全体を元 augmentation の始点／終点重複による退化二単体へ同定済み。
  側面正方形全体も単位貼り合わせへ同定済み。前側は元 augmentation と第二 Hom 入力、後側は元 augmentation と第一 Hom 入力を全時間で保持する実合成対応内のホモトピーへ接続済み。
  前正規化を経た後側入力は元の左 Hom 鎖射影へ厳密に同定済み。前側入力も元の右鎖射影の同じ区間族を回収する。
  native 四補正族は正本導来 augmentation と元左右 Hom 入力を全時間で保つ入力 fiber 内の実ホモトピーへ接続済み。
  同じ Hom 模型同型の逆で主経路のパラメーターへ移し、元端は正本第一・第二入力 lift、補正端は単位補正との共通端へ厳密に同定済み。
  標準係数端も同じ coherent 三角形全体と元入力の一致で正本係数 lift へ同定済み。終側標準面は同じ四面体の第零面を使う。
  実四補正道と選択済み二変形の三辺を保持する相対充填・合成三角形・対角後合成を供給済み。二次元全域で元左右鎖射影を固定する。
  主経路上の六片は五頂点・六実合成構造・全共有辺・二補正辺・係数辺・橋を保持する。二つの実単位閉路の零性だけを入力として指定境界を充填する④の入口まで接続済み。D-13 の両単位則を全三角形の σ₀・σ₁ 退化へ移し、同じ射影四面体の二単位面へ接続済み。左閉路は Λ³₂ の相対比較、右閉路は全正方形の厳密退化で零性を証明し、指定三辺の境界充填を無仮定で供給済み。

### G-1 d の三段目（固定）
- [x] ① 未追跡2ファイルの修正・個別検証・集約／監査への接続。
- [x] ② 正規化 prism を canonical 導来係数の実区間面へ照合。
- [x] ③ cube の入力固定変形と既存の選択変形を、二次元相対比較で接続。
- [x] ④ `dgGluingLaxHomDiagonalComparisonBoundary` の指定境界を保持して充填。
- [ ] ⑤ 正本 `dgGluingLaxHomPullbackComparison` の実ホモトピー逆と往復則を構成。
- [ ] ⑥ 充満忠実性・既存の本質的全射性から比較同値と全試験関手の ∞ 普遍性を供給。

### 残り（依存順）
1. (d) 上の⑤〜⑥。Tamme Remark 6、F0 の判定。見積り 2〜3 日。
2. (e) 安定性・完全射影と F2 の `laxPullback_isStable`・K-8b の半直交分解との整合。Tamme Lemma 8。見積り 1 日。
3. (f) 通常 pullback と Verdier 商 ⊙ の dg 同定、K-8 d8 の `IsVerdierSequence` の供給。D-9 と共同。
   Tamme §1、Drinfeld Thm 3.4、β3 の平坦商。見積り 2〜3 日。完了時に D 向けの引き継ぎを整えて停止する。

### 主要宣言（型は Lean が正本）
- `DGGluingObject`・`dgGluingDifference`・`dgGluingHomComplex`・`dgGluingDGCategory`・`dgGluingToComma`
- `dgGluing_isDGPretriangulated`・`dgGluingFactors_semiorthogonal`・`dgGluingDecompositionTriangle_distinguished`
- `dgGluingUniverseDerivedNerveLaxComparison`・`dgGluingUniverseDerivedNerveLaxComparison_isEssentiallySurjective`
- `dgGluingUniverseDerivedNerveLaxComparison_fullyFaithful_iff`・`dgGluingLaxHomPullbackComparison`
- `dgGluingLaxHomLeftModelComparison_eq`・`dgGluingLaxHomRightModelComparison_eq`
- `dgGluingHomDerivedCompositionInputPathComparison_equivalence`・`dgGluingLaxHomInputStrictComparison`
- `dgGluingNativeDerivedPreNormalizeCube`・`dgGluingNativeDerivedPostNormalizeCube`・`dgGluingNativeDerivedNormalizationCube_shared_face`
- `dgGluingNativeNormalizationFirstTriangle_eq`・`dgGluingNativeNormalizationLastTriangle_eq`
- `dgGluingCoefficientYonedaSpaceIso_inv_chainMap`・`dgGluingNativeCoefficientDomainIso_inv`
- `dgGluingNativeNormalizedPrism_canonical_coefficient`・`dgGluingNativeDerivedPostNormalizeCube_canonical_interval_face`
- `dgGluingNativeDerivedNormalizedIntervalPrism_normalization_exists`
- `dgGluingLaxHomFirstInputHomotopy_relative_comparison`・`dgGluingLaxHomLastInputHomotopy_relative_comparison`
- `dgGluingNativePreNormalizeTriangleFamily`・`dgGluingNativePostNormalizeTriangleFamily`
- `dgGluingNativeNormalizationPasting`・`DGGluingNormalizationProjectionInput`
- `dgGluingNormalizationCompositionTetrahedron`・`dgGluingNativeNormalizationAugmentationTetrahedron`
- `dgGluingNormalizationAugmentationTetrahedronHomotopy`・`dgGluingInputHomotopy_post_homMk_eq`
- `dgGluingHomotopyTriangleFilling_iff`・`dgGluingHomotopyTriangleFilling_transfer`
- `dgGluingLaxHomDiagonalComparisonBoundary_filling_of_input_triangle`
- `dgGluingLaxHomDiagonalComparisonBoundary`・`dgGluingLaxHomFirstInputHomotopy_over`・`dgGluingLaxHomLastInputHomotopy_over`

### 依存と提供
- 読み取り専用：`Derived/` の β5・β3、`F2/CatInfinity/`、`Core/`・`F1/`・`F1B/`。
- 提供先：Sp（K-8 の ⊙）、K-B・K-S•（具体的 Verdier 列）。D2 の f 完了後は D が Gluing を吸収。
- β5 の入口：`dgAlgebraDerivedInfinityCategory`、`Bimodule`、`Morita.kernelTensor`、`dgKernelDerivedInfinity`。
- D の Small 不要 Direct prism 自然性は `059a227ad`。coherent prism 自身の自然性は追加供給 `9b40d1218`。
  入口は `DGPinchedCompositionClosedFamilyNaturality` の `dgPinchedCompositionFamilyPrism_closed_first_naturality`／`closed_second_naturality`。
- `dgGluingNormalizationProjectionInput_naturality` で六等式を無仮定で実例化済み。全標準面と固定標的輸送を保持する。
  標準面の恒等入力射影・前後終側の replacement 全三角形の一致は照合済み。厳密両単位則は D-13 で供給済み。両単位は主経路へ接続済み。F1B の公開 `RelativeDiagramHomotopy` を直接利用し、Λ³₂ を固定した相対四面体比較の存在は実例化済み。

### 設計上の確認点・次の一手
- 前 cube の正規化端は `dgGluingIdentityCommaObject` を始対象とする。第一三角形の固定辺は元 augmentation から恒等辺へ変わる。
  したがって、全時間の第一三角形族をそのまま元の始辺固定入力 fiber 内のホモトピーとは扱えない。
- **採用（2026-10-24、コーディネータ指示）**：共有面と側面の標準合成三角形も含む貼り合わせを先に構成し、その相対二次元比較を選択済み二変形へ移す。
  二つの cube それぞれの三角形族を直接、元の固定辺を保つ入力 fiber へ入れる前提を置かない。
  隔離していた射影自然性（前後・終側の三角形それぞれ二射影、計六等式）は、追加供給により実例化済み。
  公開界面と三段目③〜⑥の順序は不変。三段目の完了では停止しない。
- **再開（2026-10-24、コーディネータ指示）**：D の追加供給を接続済み。元固定辺を保つ側面補正と、実入力二変形・その合成三角形の構成を続ける。
  公開界面・採用済み貼り合わせ経路・③〜⑥の順序は不変。
- 正本は `dgGluingLaxHomPullbackComparison`。元の両 Hom 入力・augmentation prism・二三角形を保持する。
  個別の入力固定ホモトピーだけから全 path 比較の一致を結論しない。主経路へ新しい仮定を追加しない。

### 未コミット・既知の問題
- 検証済み：集約ビルド 8926 jobs、公理監査 879 モジュール・8244 宣言。許容三公理のみ。新規 sorry・axiom・主経路 ModelCategory 仮定なし。
  ログ：`/tmp/d2-v3-raw-input-coordinates-aggregate-build.log`・`/tmp/d2-v3-raw-input-coordinates-audit.log`。指定充填と入力付き path の実逆射・両往復変形を無条件で接続済み。同一対角・元二入力を持つ四座標比較まで同値性を移送済み。四座標の厳密同型と元矢印・左右鎖射影を回収する。
- 検証済み部分をコミットし、正本標的から元二入力と二合成対応を持つ区間座標への実同値を構成済み。元正本比較の矢印射影と左右 Hom 鎖射影を厳密に回収し、既存の四座標比較の両射影との一致を供給済み。底の二作用を照合中。数学的未完は⑤〜⑥・e・f。
- β5 の Bimodule は第一 dg 圏に反変、第二に共変。KL の φ(d,c) は `M.value c d`、比較差は `gμ − νf`。

## 規約
- 配置：`SerrePositivity/InfinityCategories/Derived/Gluing/`。集約：`Derived/Gluing.lean`。監査：`scripts/audit_derived_gluing.lean`。
- foundations.md §8 v3。所有ファイルのみ `set -o pipefail` のうえ `git commit --only`。他レーンは読み取り専用。
- 新規 sorry・公理・引用なし。主経路へ ModelCategory 仮定を入れず、heartbeat 上限は増やさない。移動・改名・削除は R の停止窓。
- 原典：Tamme 2018 §1、Kuznetsov–Lunts、Drinfeld 2004。実施記録はコミットメッセージ。計画本文は300行以内。
