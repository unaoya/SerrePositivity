# D-e：D-8 e の実 perfect 比較と D-8 d の covers

## 再割当：strict bar 比較 C1・C2（2026-10-25）

- 現在地：C1・C2 完了。元の coherent G のホモロジー図式と実 bar の
  単体次元フィルトレーション、実部分複体の段階模型とその余極限性まで構成。
  一次成分の閉性、高次 HA の二段下降、零段階での theta 消滅も構成。
  通常のホモロジー図式の増大 simplicial bar と、実 bar への頂点の閉零射を公開。
  filtered poset 上の通常のホモロジー bar の全正次数完全性と
  零次ホモロジー＝余極限を構成。実 bar の隣接段階と内部次元層の短完全列も構成。
  通常の bar の splitting と非退化複体へのホモトピー同値、非退化側の完全性、
  非有界加群複体の直和のホモロジー比較も構成。
  実次元層のホモロジーと非退化ホモロジー bar の対象同型、
  実長完全列による一次複体と二乗零、連結射の cycle 代表元公式まで構成。
  非退化 bar の実微分の交代面和公式、高次 HA 列の直下層への射影零、
  層ホモロジー同型と各非退化係数包含の可換性も構成。
  連続 shift 単位の符号と一次列の外側の符号の相殺、
  閉じた次数一層作用素、その cycle 上の評価と実連結射との一致も構成。
  元の正の面ブロックと一次 prefix ブロックのホモロジーを、
  端点等号射と元の閉零 prefix 係数から作る実加群射へ同定した。
  prefix の実加群射を元の図式の辺へ同定し、ホモロジー図式の関手の射との
  可換式も構成。正の面の係数の恒等性も同じ頂点ホモロジー同型で検証した。
  総次数を指定する自然な実層ホモロジー同型と各包含の式を構成。
  正・零の両面について、通常の bar と同じ添字・同じ係数射への比較を構成。
  一次微分全体の交代面和と、実長完全列の一次複体から非退化 bar への
  複体同型を構成。一次複体の正次数完全性と零次＝余極限も構成。
  有限 support の cycle と境界の下降により零段階からの全射性と核を同定。
  実ホモロジーを一次微分の余核に同定し、全 coherent 入力に対する
  `dgCoherentBarHomologyColimitIso` を構成済み。strict 標準射そのものの擬同型性も構成済み。
  strict/coherent ホモロジー図式の自然同型、標的の filtered ホモロジー
  余極限同型と全脚の可換性、実増大と graded 増大の全成分の一致、
  零段階での増大比較、非退化 bar の標準増大の余核性を構成。
- 所有追加：`Derived/CoherentBar/StrictComparison/` の新規葉とその `All`、
  `scripts/audit_derived_coherent_bar_strict.lean`。既存 CoherentBar は読み取り専用。
- 主定理の入力修正：κ-filtered poset 上でも native 図式は coherent のまま。
  G は bar と同じ HA 成分つき入力とし、各評価 x・次数 q で
  `H_q(normalized bar(G)(x)) ≅ colim_j H_q(G_j(x))` を先に示す。
  strict augmentation の擬同型性はその特殊化として導く。
- 三段目：1 coherent G のホモロジー図式、2 実 bar の単体次元フィルトレーション、
  3 有限 support と filtered 完全性によるホモロジー比較、4 strict 版の特殊化、
  5 自分の集約・専用監査・限定保存、6 B 到着後の比較値と無条件 covers。
- h-projective 頂点の実正規化 bar の射影性まで構成・集約検証済み。
  実 MC 段階、隣接段階の全次数分裂、段階の実余極限を構成し、
  Hom 塔の非輪体性で全体へ接続（可算 telescope の Hom 側の判定）。
- 射影的模型での指定 bar 余錐の余極限性と、半自由模型での任意の小さい
  coherent 図式の余極限の存在まで接続済み。指定余錐からの実 dg 増大、
  余核による一般擬同型判定、native 余錐のホモロジー余錐、
  coherent ホモトピーのホモロジー自然同型と指定成分公式も構成。
- 分解 augmentation のホモロジー自然同型、指定 strict 余錐の native 化、
  分解後の拡張ホモロジー余錐の余極限性まで構成。
  bar から射影的頂点への擬同型による、半自由 native 余極限頂点の指定も構成。
  正本の strict 導来図式との全関手同型、零次元層の実 dg 包含、
  C1 増大への同定、native 零次元列との一致まで検証。
- 指定増大射の零次元係数からホモロジー余核比較へ接続済み。
  `dgBarCoconeUniversal_quasiIso_of_homologyColimit` と
  `dgSemifreeCoherent_vertexComparison_of_homologyColimit` を構成。
  終頂点付加図式のホモロジー余錐の比較も接続済み。
  `dgKappaStrictFilteredColimitComparison_unconditional` は正則 κ のみを入力とする
  `DGKappaStrictFilteredColimitComparison R D κ` の無条件値。
  `dgKappaCone_covers_unconditional` は比較引数を持たず、正則非可算 κ の
  全 κ-compact 頂点を同じ実代表系で被覆する。
  非有界複体なので、有限 support の最大単体次元を下げる証明で収束を扱う。
  高次 HA 項を零とはせず、単体次元を二つ以上下げる項として扱う。
  工程 B の余錐と普遍性は射影的 bar を介して半自由模型へ接続済み。
- C1 最終公開名：`dgCoherentBarHomologyColimitIso`、
  `dgCoherentBarStrictColimitAugmentation_quasiIso`、
  `dgKappaCoherentBarHomologyColimitIso`、
  `dgKappaStrictBarColimitAugmentation_quasiIso`。
- 初期補助宣言：`dgCoherentBarStrictDiagram`、`dgCoherentBarStrictNormalizedModule`、
  `dgCoherentBarStrictAugmentationGraded`、`dgCoherentBarStrictColumn`、
  `dgStrictFilteredColimit_quasiIso`。
- 依存：D-bar の正規化加群と公開 MC、Mathlib の ModuleCat AB5 と複体の関手。
  B は 87ecf98c0 の無条件 native 余極限定理を読み取り専用で消費。
  ただし B の標的は全加群の dg nerve、比較述語の標的は半自由模型。
  ユーザー指示により bar の h-projective 性を単体次元フィルトレーションで構成。
  任意の小さい直和は既存 moduleCoproduct_homotopicallyProjective を再利用。
  実導来 bar 余錐の全単体の接続と C1 の頂点同型、消費側の還元は構成済み。
  次元上限つき直和の分裂射影、包含に沿う MC 制限も構成済み。
  C2 の無条件値と covers の無条件系まで集約ビルド済み。
- 保存：9fe01e67a に検証済み22葉を限定保存。その後、実 augmentation と
  自己 Hom の MC 微分公式を仕上げ、集約3,717 jobs成功。
- 検証：coherent 入力への修正後、集約9,981 jobs・専用監査209葉1799宣言通過。
  許容三公理のみ。coherent 主定理と strict 標準射の C1 を完了。
- coherent 版の実装：各評価・各次数のホモロジー図式、実正規化 theta の
  単体次元による Hom 支持、内部微分による支持保存、theta による一段下降、
  高次 HA prefix の二段以上下降、任意の元の有限 support と次元上限。
  評価複体の実部分複体、段同士の包含、段階模型の実余極限性を構成。
  ホモロジー図式の射と元の辺の鎖写像によるホモロジー射の自然性も検証済み。
  一次列の内部閉性、高次列の二段下降、零段階 theta 消滅、
  通常の増大 simplicial bar、実正規化 bar への頂点の閉零射も構成。
- 主要追加名：`dgCoherentBarStrictColimitAugmentation`、`dgStrictNormalizedEndRebase_d`。
- 次の一手：対象同型を通して一次ホモロジー微分と非退化 bar 微分を同定する。
  面・辺の個別係数の同定を、層の直和同型を通して有限面和へまとめる。
  `dgHomologyBarZeroHomologyColimitIso` が通常の bar の零次の比較。
  `dgCoherentBarLayerSequence_shortExact` が実複体の隣接段階の短完全列。
  正次数完全性は有限 support を終頂点のある下方部分圏へ持ち上げ、
  局所縮約で boundary を得て全体へ戻す形で証明した。
  `dgHomologyBarFiltered_exactAt` がこの全正次数の公開名。
  strict 版の既存部品は保持するが、一般の G を strict と仮定しない。

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
