# D-e：D-8 e の実 perfect 比較と D-8 d の準備

## 引き継ぎ（2026-10-25）

- 現在地：D-8 e 完了（5bf80c07c）。D-8 d は提案文の採用状況を確認中。
  可逆な準備として compact→段階 retract、同じ代表族の retract 被覆、
  依存閉ラベルの κ-filtered 添字と自由余積層の strict 余極限を実装。
  D-8 d の全 covers は未完。
- 所有：`Derived/KappaPerfect/` の新規葉と `All.lean`、
  `scripts/audit_derived_kappa_perfect.lean`、本計画。追加候補は
  `Derived/KappaCovers/` の新規葉と `All.lean`。
- 読み取り専用：既存 D 全体・D 集約と両監査、KST 全体。
- 残り：D-8 d 担当移管の採用確認。採用時は一般 semifree 加群の cell ラベル抽出、
  依存閉部分集合上の実 cell 部分加群と strict 余極限、各段の同じ代表系による被覆、
  D-bar の native/strict 比較入力、最終 covers。
- 主要宣言：`dgKappaPerfect_stableClosure_iff`、`dgKappaPerfectToPerf`、
  `dgKappaPerfectReverse_isQCatEquivalence`、`dgKappaPerfectReverse_inclusionIso`、
  `dgKappaPerfectComparison`、`dgKappaPerfectComparison_isQCatEquivalence`、
  `dgKappaPerfectComparison_inclusionIso`、`dgKappaPerfectInput`。
- 依存と提供：K-B の `DGKappaConeInput` を明示入力として、
  `DGKappaPerfectInput` の三欄を D 側で構成する。
- 保存：D-8 e は所有7ファイルを限定保存済み。D-8 d の準備も限定保存する。
  共有作業木の他レーン差分は含めない。
- 既知の問題：他レーンへの依頼なし。D-8 c/d の供給自体は本レーンの結論ではない。
- 次の一手：採用状況の回答に従う。継続なら下記 d1 の一般 cell ラベル抽出。

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


## D-8 d の三段目（担当移管の採用確認中）

1. [ ] κ-small cell 部分加群の添字圏・図式・strict 余極限表示。
   DependencyPieces は可算依存先の閉包の κ-small 性・全ラベル被覆・
   全 coherent 図式に対する κ-filtered 性を供給する。
   SubsetCoproduct は自由余積層の通常の余極限を供給する。
   twisted differential を保つ cell 部分加群や一般 semifree 表示の存在は未結論。
2. [ ] D-bar の native/strict 比較をその結論の型で仮定引数に取り、native 表示へ接続。
   CompactStage の `hc : IsColimitCone c` は使用箇所の最小境界であり、
   D-bar の一般比較そのものを構成したものではない。
3. [x] 全 Hom の compact 性から同じ native 図式の一段の retract を回収。
   `dgKappaCompact_retract_of_nativeCellPresentation`。
4. [x] 同じ選択代表系の native retract を同じ集合内の代表との VertexIso で被覆。
   `dgKappaClosedProjectiveObjects_nativeRetractCovers`。
   対象集合の零・shift・cone・可算直和閉性から h 本質像の三角閉性を作り、
   指定 telescope cone の分裂で retract 閉性を導出する。
   二端点の射影性で主導来 retract を K(D) へ反映し、native VertexIso へ戻す。
   D-16 の thick 核を新たな入力にしない。
5. [ ] 一般の κ-compact 頂点に対する最終 covers・監査・限定コミット。
   途中成果を検証して保存しても、この工程の完了とは数えない。

### D-8 d 準備成果の検証

- `lake build SerrePositivity.InfinityCategories.Derived.KappaCovers.All`：9,342 jobs 成功。
- 既存の自分の監査に KappaCovers の7葉を追加。合計11葉・107宣言で成功。
- 許容三公理のみ。新規公理・sorry・ModelCategory 仮定なし。
- 追加10ファイルだけを `git commit --only` で保存する。
- 最終 covers の公開名はまだない。準備成果を D-8 d 完了とは扱わない。

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

### 採用確認の理由

ユーザー文の「ユーザー判断待ちの提案。採用時に貼る」という留保と
「続けて D-8 d を担当する」が併記されているため、採用済みかを確認中。
確認中は新しい cell 模型の実装を止め、既存の準備成果の監査・保存だけを行う。
無回答を採用とは扱わない。D-8 e の完成状態は維持する。
