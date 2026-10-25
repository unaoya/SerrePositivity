# D-e：D-8 e の実 perfect 比較と D-8 d の covers

## 再割当：strict bar 比較 C1・C2（2026-10-25）

- 現在地：C1 続行中。strict 図式、graded augmentation の全 theta 消滅、
  dg 加群の filtered strict 余極限による擬同型保存、有限 support の共通上界、
  末尾付加の次数 −1 作用素と実正規化 MC 加群への移送まで構成。
  実正規化 bar から strict 余極限への標準 dg 射と、実自己 Hom の MC 微分公式も構成。
  局所縮約恒等式と最終擬同型性はまだ未完。
- 所有追加：`Derived/CoherentBar/StrictComparison/` の新規葉とその `All`、
  `scripts/audit_derived_coherent_bar_strict.lean`。既存 CoherentBar は読み取り専用。
- 三段目：1 strict 図式と標準射の型、2 正規化 augmentation、3 filtered 完全性と
  局所縮約による擬同型性、4 自分の集約・専用監査・限定保存、
  5 工程 B 到着後に比較値と covers の無条件の系。
- 残り：末尾付加の局所縮約恒等式、
  filtered 完全性への接続（C1、8–24時間）。工程 B の余錐と普遍性の代入
  （C2、B 到着後1–3時間）。
- 主要宣言：`dgCoherentBarStrictDiagram`、`dgCoherentBarStrictNormalizedModule`、
  `dgCoherentBarStrictAugmentationGraded`、`dgCoherentBarStrictColumn`、
  `dgStrictFilteredColimit_quasiIso`。
- 依存：D-bar の正規化加群と公開 MC、Mathlib の ModuleCat AB5 と複体の関手。
  C1 の証明へ native 普遍性を仮定していない。B は現計画で未構成。
- 保存：9fe01e67a に検証済み22葉を限定保存。その後、実 augmentation と
  自己 Hom の MC 微分公式を仕上げ、集約3,717 jobs成功。
- 検証：専用監査24葉203宣言通過、許容三公理のみ。C1 完了とは扱わない。
- 主要追加名：`dgCoherentBarStrictColimitAugmentation`、`dgStrictNormalizedEndRebase_d`。
- 次の一手：末尾付加作用素の bar 微分を計算し、有限 support 上で縮約恒等式を示す。

## 引き継ぎ（2026-10-25）

- 現在地：D-8 e 完了（5bf80c07c）。採用済み D-8 d も、指定された
  D-bar 比較の明示引数の下で最終 covers まで構成・ビルド済み。
- 所有：`Derived/KappaPerfect/` の新規葉と `All.lean`、
  `scripts/audit_derived_kappa_perfect.lean`、本計画。追加所有は
  `Derived/KappaCovers/` の新規葉と `All.lean`。
- 読み取り専用：既存 D 全体・D 集約と両監査、KST 全体。
- 外部境界：D-bar の native/strict 比較の証明は明示引数。
  cell 表示の存在・各段の代表化・compact retract・代表系の retract 閉性は構成済み。
- 主要宣言：`dgKappaPerfect_stableClosure_iff`、`dgKappaPerfectToPerf`、
  `dgKappaPerfectReverse_isQCatEquivalence`、`dgKappaPerfectReverse_inclusionIso`、
  `dgKappaPerfectComparison`、`dgKappaPerfectComparison_isQCatEquivalence`、
  `dgKappaPerfectComparison_inclusionIso`、`dgKappaPerfectInput`。
- 依存と提供：K-B の `DGKappaConeInput` を明示入力として、
  `DGKappaPerfectInput` の三欄を D 側で構成する。
- 保存：D-8 e は所有7ファイルを限定保存済み。D-8 d の検証済み中間成果は
  1c7443f4a・c07d8a799。最終分も所有ファイルだけを限定保存する。
  共有作業木の他レーン差分は含めない。
- 既知の問題：D-8 c と D-bar 比較自体の実装には依存しない。
  比較の証明が届いたら最終定理の引数へ代入できる。
- 次の一手：最終監査・限定保存・公開名の報告後、指定どおり停止する。

## D-8 e の三段目

1. [x] 同じ κ-cone の perfect 安定閉包の条件と元の perfect 条件を同定する。
2. [x] 同じ加群と全 Hom を保つ逆向き dg 関手を構成し、
   perfectCovers から本質的全射性を供給する。
3. [x] 全写像空間での QCat 同値から、元の実 Perf を始域とする逆を取る。
4. [x] 実出力分解の augmentation と半自由・射影的同値の余単位により、
   β5 の包含との全関手同型を供給し、正本の三欄を束ねる。
5. [x] 自分の集約・監査だけを検証し、`git commit --only` で保存、公開名を報告して停止。

## 構成

`Closure` は同じ cone の実加群値 dg 関手の完全性を宇宙降下し、
主導来加群圏の perfect 三角的対象条件を native h に戻す。
`stableHoClosure_le_iff` により安定閉包が元の perfect 条件から出ないことを示す。
retract 閉包を安定閉包の定義へ追加しない。

`Equivalence` の `dgKappaPerfectToPerf` は同じ加群を元の
射影的 perfect 加群の dg 模型へ送り、全 dg Hom の写像は恒等。
このため native 写像空間で充満忠実である。
`perfectCovers` の主導来同型は D-21 の Perf h 比較で頂点同型に戻し、
本質的全射性だけに用いる。通常の Hom 同型から全写像空間同値を推論しない。

`Inclusion` は同じ加群値関手の実出力分解と元の射影的出力の全関手同型、
前合成比較、および半自由包含の充満忠実性で包含同型を構成する。
`Input` は逆向き QCat 同値の選択した逆を comparison とし、
余単位で inclusion を逆向きへ輸送する。

## 依存境界

- `DGKappaConeInput` 自体の実例は D-8 c/d の供給を待つ明示入力。
- 本体が使用するデータは同じ対象集合・小ささ・前三角性・射影性・perfectCovers。
  κ-compact 性、全 κ-compact 被覆、可算 swindle をこの証明には使わない。
- D-8 a/b の実代表系に対して、後で構成される同じ入力にそのまま適用できる。
- D-16 の thick 核と retract の同定や D-21 の冪等完備化を新たな仮定にしない。
  本比較では perfect 対象を初めからすべて生成集合に含むため、
  追加の retract 代表化は不要。D-21 の実 Perf h 比較だけを再利用する。
- KST からの直接 import は正本 `DGKappaPerfectInput` のみ。
  所有外の既存ファイル・集約・監査は変更しない。

## 消費入口

`public import SerrePositivity.InfinityCategories.Derived.KappaPerfect.All`

namespace は `SerrePositivity.InfinityCategories`。
`dgKappaPerfectInput R D I : KST.NonConnective.DGKappaPerfectInput R D I`。
比較を追加仮定にせず、同じ `I` の実データから三欄を構成する。
`I.derivedFullyFaithful` を別に仮定する必要もなく、逆向き dg 関手が
全 Hom の恒等写像であることから充満忠実性を直接証明する。

## 検証

- 結果：集約 9,162 jobs 成功、監査 4 葉・49 宣言成功（許容三公理のみ）。
- 集約：`lake build SerrePositivity.InfinityCategories.Derived.KappaPerfect.All`
- 監査：`lake env lean scripts/audit_derived_kappa_perfect.lean`
- 監査は新規四葉の全宣言の推移的公理を調べ、
  `propext`・`Classical.choice`・`Quot.sound` だけを許可する。
  新規公理と署名の ModelCategory 仮定も拒否する。
- 主経路の三欄と最終入力の型を `#check` で明示する。
- 新規 sorry・引用公理・`ModelCategory SSet` なし。
- 公開名を報告後に停止。共有計画・共有集約への統合はコーディネータ所有。


## D-8 d の三段目（採用済み）

1. [x] κ-small cell 部分加群の添字圏・図式・strict 余極限表示。
   標準 resolution の有限段の斉次要素に有限セル support を与え、各 kernel cell の
   境界の依存先を固定する。依存閉選択の自由 disk・実 cone を帰納し、
   比較の単射性と要素の持上げを保持する。可算余極限の実 semifree filtration を作り、
   各自由層の κ-small 性から同じ代表系で被覆する。
   依存閉選択全体を κ-filtered 関手にし、単射性と網羅性から strict 余極限性を得る。
2. [x] D-bar の native/strict 比較をその結論の型で仮定引数に取り、native 表示へ接続。
   `DGKappaStrictFilteredColimitComparison` は同じ strict 図式の全単体上の像を固定する。
   追加の cell 表示存在仮定は要求しない。
3. [x] 全 Hom の compact 性から同じ native 図式の一段の retract を回収。
   `dgKappaCompact_retract_of_nativeCellPresentation`。
4. [x] 同じ選択代表系の native retract を同じ集合内の代表との VertexIso で被覆。
   `dgKappaClosedProjectiveObjects_nativeRetractCovers`。
   対象集合の零・shift・cone・可算直和閉性から h 本質像の三角閉性を作り、
   指定 telescope cone の分裂で retract 閉性を導出する。
   二端点の射影性で主導来 retract を K(D) へ反映し、native VertexIso へ戻す。
   D-16 の thick 核を新たな入力にしない。
5. [x] 一般の κ-compact 頂点に対する最終 covers を構成・ビルド。
   自分の集約・監査だけを検証し、所有ファイルだけを `git commit --only` で保存する。

### D-8 d の検証

- `lake build SerrePositivity.InfinityCategories.Derived.KappaCovers.All`：9,370 jobs 成功。
- 自分の監査を KappaCovers 全31葉と KappaPerfect 全4葉に拡張。
- 許容三公理のみ。新規公理・sorry・ModelCategory 仮定なし。
- 最終 covers は D-bar 比較の下で完成。比較自体の証明を構成したとは主張しない。

### D-8 d の主要公開名

- `dgKappaCone_covers_of_strictFilteredColimitComparison`
  ：`DGKappaConeInput.covers` と同じ全 κ-compact 頂点の被覆型。
- `dgKappaResolutionStrictRepresentativePresentation`
  ：任意の実加群の標準 resolution の実 κ-filtered strict 表示。
- `dgKappaResolutionPiecesDiagram`・`dgKappaResolutionPiecesIsColimit`
  ：依存閉部分 cell 加群の実関手と余極限性。
- `dgKappaPartialResolution_representativeCovers`
  ：κ-small 部分 cell 加群の同じ代表系による被覆。
- `DGKappaStrictFilteredColimitComparison`
  ：D-bar 側から代入する唯一の外部比較命題。

### D-8 d の公開補助名

- `dgKappaCompact_classicalRetract_of_nativeCellPresentation`
- `idempotentTelescope_fixedCone_splits`、`idempotentTelescope_fixedCone_iso`
- `triangulatedProperty_of_retract_countable`
- `dgKappaCoversImage_iff`、`dgKappaCoversImage_isTriangulated`
- `dgKappaCoversImage_countable`、`dgKappaCoversImage_of_retract`
- `dgKappaClosedProjectiveObjects_homotopyRetractCovers`
- `dgProjective_homotopyRetract_of_derivedRetract`
- `dgKappaClosedProjectiveObjects_nativeRetractCovers`
- `dgKappaDependencyClosure_small`、`dgKappaDependencyPieces_cover`
- `dgKappaDependencyPieces_nerve_isKappaFiltered`
- `dgKappaSubsetCoproductIsColimit`

### 採用済みの運用

D-8 d の移管はユーザーが明示採用済みと回答。報告後は承認を待たず続行する。
native/strict 比較は D-bar の結論の型を仮定引数として保持し、届いたら代入する。
D-8 d の完成と D-bar の比較構成自体の完成を区別する。

### 採用後の実装進捗

- `DGKappaStrictFilteredColimitComparison`：固定した strict 図式を native 図式へ
  送る D-bar 側の必要な結論の型。頂点だけの比較には弱めていない。
- `dgKappaCovers_of_strictRepresentativePresentation`：strict 表示を消費して
  正本 `covers` と同じ型の結論を得る。表示の存在定理ではない。
- `dgKappaClosedProjectiveObjects_smallSemifreeCovers`：各自由層の添字が
  κ-small な実 semifree 加群を代表系で K(D) 同型まで被覆。
- `dgKappaSubsetModule_finiteElement`：実余積の有限部分族への斉次要素の持上げ。
- `dgKappaModuleConeMap_degreewiseMono`：部分 cell 付加の比較の次数ごとの単射性。
- `dgKappaResolutionElement_finiteSupport`：標準 resolution の有限段の有限セル support。
- 依存閉選択の実部分 cell 列・その κ-filtered strict 余極限・代表化を最終定理へ接続済み。
- 中間検証：集約9,357 jobs・監査24葉318宣言で成功。
  最終集約9,370 jobs・最終監査35葉454宣言で成功。
  新規公理・sorry・ModelCategory 仮定なし。推移的公理は許容三公理のみ。
