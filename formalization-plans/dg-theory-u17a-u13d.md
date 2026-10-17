# U17a・U13d の実装記録

正本：`dg-theory.md` §15.7 U17a、§15.3 U13d、§17.86–17.87。

最終状態：U17a・U13d 完了。compact ⇔ Perf は引用なしで証明した。
対象ビルド・主要53宣言の公理監査を実施し、全て標準3公理のみ。

## 担当・境界

- U17a は `DifferentialGraded/Verdier/` に新設する。既存の有限 cell・Perf・Mathlib の三角構造と指定局所化を再利用する。
- U17b/c の受け渡し先として既存 `karoubiVerdierOrderEquivalence`、`paperRankEquivalence`、`paperSequenceComparison` の型を先に確認した。
- U13d は引用なしの compact ⇒ Perf を検討・実装する。DG-PER 採用が必要となれば採用せずに停止して報告する。
- 既存の dg 合成・KFlatBimodule・cell 系・Quotient・Endomorphism と既存一般論は編集しない。
- 新規ファイルの同名有無を事前確認。新規 sorry・axiom・引用なし。amend・rebase・reset なし。
- ルート import は自分の hunk だけを部分 stage。正本には参照一行のみを追加する。

## 型と数学的区別

`tria(D)` は既存 `DerivedFiniteCellCategoryOver A D Set.univ` を用いる。
S⊆D は明示的 dg 商の full 部分圏と同じ対象添字。S の代表加群の三角閉包を tria(D) 内に取り、
商はその `trW.Localization`、U17b の比較先は既存 `Karoubi` を施した型とする。

一般の Verdier 商の核は三角部分圏の retract 閉包であり、tria(S) そのものと無条件に同一視しない。
Mathlib の `triangEnvelope` は retract も含む厚い閉包なので、その区別を公開 API に保持する。
Karoubi を先に取った側は既存 `karoubiNullEnvelope` をそのまま使う。

## U17a（完了）

- `Verdier/Tria.lean`：既存の有限 cell 本質像を `TriaCategory` とし、
  `triaImage_le_iff_generators` で S の代表対象を含む最小の三角部分圏であることを証明。
- `Verdier/NullObjects.lean`：既存の Verdier 分数計算と三角形の Hom 完全性から
  `verdierQuotient_isZero_iff_retractClosure` を証明。商で恒等射が零なら、分母射を零にでき、
  その錐への retract が得られる。逆は三角関手の核の retract 閉性。
- `triaQuotient_isZero_iff_triaNull` と `triaQuotient_isZero_iff_perfect` で、
  零対象の逆像・thick 閉包・既存の Perf_S の制限が一致する。
- U17b の比較先は `CompletedTriaQuotient`。U17c へは既存の
  `karoubiVerdierOrderEquivalence` をそのまま用い、`triaKaroubiComparison` は
  `paperSequenceComparison` と同じ向きの自然同型。U17b/c 自体を証明済みとはしない。
- A は任意の可換環、D の対象宇宙 v は係数・Hom の宇宙 u と独立、仮定は `Small.{u} D`。
  体・有界性・局所有限性は仮定しない。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.VerdierTria` 成功。
  主要10宣言の `#print axioms` は全て `propext, Classical.choice, Quot.sound` のみ。
  新規 sorry・axiom・引用なし。

## U13d（完了、以下は各段階の記録）

当初は telescope と有限因子分解の経路を検討し、以下の小単位で引用なしの証明を完成した。

### U13d2：可算 telescope の有限段階因子分解

- `Perfect/CompactConverseTelescope.lean`：任意の導来対象列 F と遷移射 d に対して、
  余積上の `1-shift` を定義。compact な始域の Hom 上で単射であることを、
  各成分への射影と自然数帰納法で証明した。shift 後も随伴の Hom 加法同型で単射。
- `moduleCompact_telescope_factor`：指定 telescope 三角形への射は有限段階 F n を経由する。
  `moduleCompact_telescope_retract`：compact な telescope 対象はある F n の retract。
  有限高さを有限個の cell と同一視していない。
- 可算添字は `ULift.{u} ℕ`。既存の u-small 余積と compact 性のまま処理し、
  導来圏全体の smallness や Hom_D の追加仮定を置かない。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.CompactConverseTelescope` 成功。
  主要8宣言の公理監査は標準3公理のみ。新規 sorry・axiom・引用なし。
- 残部：semifree filtration の余極限と telescope の比較、有限高さの無限自由 cell から
  有限 cell への因子分解。U13d 全体は未完、引用採用の必要性はまだ確定していない。
- U17a のコミット：`8c9f2e13`。

### U13d3：引用なしの Neeman 型有限因子分解

- `Perfect/CompactConverseFactor.lean`：`ModuleFiniteCellFactor` は実際の有限 cell 導来像への
  因子分解。加法・前後合成・shift に閉じ、恒等射の場合は既存 Perf_S と同値。
- 任意の compact な始域からの射がこの因子分解を持つ対象を `moduleFiniteCellFactorTarget` と定義。
  有限 cell、u-small 余積、shift に対して閉じることを証明。
- `Perfect/CompactConverseExtensions.lean`：この性質の拡大閉性を引用なしで証明。
  X→P（X compact、P 有限 cell）の錐 Z が compact であることから、
  障害射 Z→T.obj₁[1] を有限 cell Q で因子分解する。P→Q の三角形を
  元の三角形へ写して有限 cell E を作り、残差を T.obj₁ への射で処理する。
  単に三角形の両端への因子分解を独立に選ぶ不十分な議論は用いていない。
- その結果、この対象クラスは三角部分圏であり、任意の指定 telescope 三角形でも閉じる。
  `modulePerfectOver_of_compact_factorTarget` は明示した有限因子分解性から Perf を導く補題であり、
  compact ⇒ Perf の無条件の結論を先取りしない。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.CompactConverseFactor` 成功。
  主要15宣言の公理監査は標準3公理のみ。新規 sorry・axiom・引用なし。
- 残部の中心は標準解像度の余極限と telescope の接続。標準解像度の各段は既存の
  自由 sphere 余積と実際の cone により扱えるため、一般 semifree の各有限部分 cell を
  明示列挙する経路は必要でない見込み。U13d 全体の完了はまだ主張しない。
- U13d2 のコミット：`ce02b5b9`。

### U13d4：標準解像度の各段への接続

- `Perfect/CompactConverseResolutionStages.lean`：自由 sphere を代表加群の shift と単位同型で
  有限 cell と同定。small な添字の再添字付けと、既存の射影加群の導来余積 cofan を再利用し、
  無限自由 sphere 余積が有限因子分解性を持つことを証明した。
- `moduleFiniteCellFactorTarget_resolutionStage`：既存の標準解像度の全ての段階がこの性質を持つ。
  初段の自由 disk 余積は objectwise acyclic で、ModuleCat の AB4 と既存の exact colimit 補題を使用。
  後続段は既存の具体的 cone を使う帰納法。既存の解像度ファイルは編集していない。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.CompactConverseResolutionStages` 成功。
  主要5宣言の公理監査は標準3公理のみ。引用なし。
- U13d3 のコミット：`e9d9eea3`。残る中心は余極限と telescope の比較である。

### U13d5：余極限の cone 表示（完了）

- `Perfect/CompactConverseSequential.lean`：任意の加法圏の列について、
  実際の余極限が余積上の `1-shift` の cokernel となることを、cocone の普遍性で証明。
  ModuleCat では成分射影と元の有限 support 表示から `1-shift` の単射性を証明。
  遷移射が単射であることは仮定しない。
- 加法関手の標準余積比較と `1-shift` の可換性を証明し、評価後の次数ごとの単射性に使用。
- `Perfect/CompactConverseSequentialCone.lean`：評価後の短完全列から既存 Mathlib の
  `mappingCone.quasiIso_descShortComplex` を再利用。
  `moduleSequentialConeDesc_quasiIso` は任意の可算 dg 加群余極限への具体的 cone 射が擬同型であることを示す。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.CompactConverseSequential` 成功。
  主要11宣言の公理監査は標準3公理のみ。引用・新規 sorry・axiom なし。
- U13d4 のコミット：`ba3c7265`。

### U13d6：compact ⇔ Perf（完了）

- `Perfect/CompactConverse.lean`：標準解像度の各段が homotopically projective であることを
  既存の semifree filtration API から取得。既存の導来余積 cofan と cone 三角形を使い、
  余積とその `1-shift` の cone が有限因子分解性を持つことを証明した。
- U13d5 の具体的擬同型で標準解像度の余極限へ、既存の解像度増大射の擬同型で元の dg 加群へ
  移す。`moduleFiniteCellFactorTarget_all` は任意の主導来対象への射の有限因子分解性。
- `moduleCompact_perfect` は compact 対象の恒等射を有限 cell で因子分解して retract を与える。
  `moduleCompact_iff_perfect` で既存 Perf⇒compact と合わせた双方向判定を公開した。
- 一般可換環 A、独立な対象宇宙 v、`Small.{u} D`、既存の u-small 余積に関する compact 性を維持。
  体性・有界性・局所有限性・Hom_D の平坦性・導来圏全体の smallness を追加しない。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.CompactConverseSequential
  SerrePositivity.DifferentialGraded.Checks.CompactConverse
  SerrePositivity.DifferentialGraded.Checks.VerdierTria` 成功（2529 jobs）。
  結論4宣言の公理監査も標準3公理のみ。全段階の主要53宣言について同じ結果。
  `ZMod 4` の一対象 dg 圏でも型検証。新規 sorry・axiom・引用なし、DG-PER 不採用。
- U13d5 のコミット：`23e1774b`。
- U17b/c の実際の dg 商との比較や U13e の残部はこの単位の結論に含めない。

## 追加担当：局所 K-flat 版 U15e・U17b（進行中）

新しい目標は、既存の明示的 path 商を tria の Verdier 商と比較し、その後 perfect dg hull の
H⁰ と `CompletedTriaQuotient` を比較すること。U12e の dg 圏分解版は担当外であり、
この目標を仮定の宣言や後段の形式的合成だけに縮小しない。

### 原典照合と仮定の入口

- 原典の確認（比較定理の引用採用ではない）：
  [Drinfeld v7 §3.3–3.4、証明 §8](https://arxiv.org/html/math/0210114)、
  [Keller v5 §4.2、§4.4 Thm 4.8](https://arxiv.org/pdf/math/0601185)。
- Drinfeld の条件 (3.3) は全 x∈D・b∈B について Hom_D(x,b) が A 上 homotopically flat。
  条件 (3.4) は逆方向 Hom_D(b,x)。いずれか一方を全体として要求する。
  組ごとに向きを選べるという選言ではない。Keller の k-flat は全 Hom との tensor が
  擬同型を保存する条件で、既存の `complexKFlat_iff_preserves_quasiIso` と対応する。
- `Quotient/DerivedComparisonFlatness.lean` に `homIntoKFlat`、`homOutOfKFlat`、
  `localKFlat`、`allHomKFlat` と部分集合への制限を実装。
- `allHomKFlat_of_flat_zero` は、非零次数が零で、次数零の Hom 加群が平坦なら全 Hom が K-flat
  になることを、既存 U12a の有界平坦複体の補題から証明。M9 手順4〜8の商を取る前の
  次数零の自由列 dg 圏に合う。商の Hom が非正次数であるというだけでは K-flat を結論しない。
  T 側も T 上で同じ入力を検証する必要があり、T の A 平坦性では代用しない。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.QuotientDerivedFlatness` 成功。
  主要9宣言の公理監査は標準3公理のみ。新規 sorry・axiom・引用なし。
- この入口のプロジェクト import 依存81ファイルを走査し、`DifferentialGraded/Resolution/`、
  `Derived/KFlatBimodule*`、`Derived/Bimodule*` への依存がないことを確認。
- U15e の比較関手の完全忠実性・本質的全射、U17b の同値は未証明。
  Drinfeld §8 の path 長 filtration と Verdier 分母の比較を次に検討する。
  DG-DR の引用採用が必要と確定した場合は採用せず、必要な規模と特殊化した型を報告する。

### 共有 index に関する追加規約

コミットは常に対象パスを明示し、直後に `git show --stat HEAD` で確認する。
共有ファイルは自分の hunk のみ部分 stage し、パス指定 commit が未 stage 部分も含めるため、
HEAD からの差分全体が自分の変更だけであることも確認する。混在があればそのパスはコミットしない。
`index.lock` は削除しない。amend・rebase・reset 禁止を維持する。

今回のコミット直前に正本へ他チャットの分担更新が加わったため、正本は対象から除外した。
自分の参照一行は working tree に残し、その一行だけの cached patch を逆適用して部分 stage を解除。
他チャットの正本変更・index は変更していない。ルートは HEAD 差分が自分の import 一行のみと確認。

### U15e2：代表対象の零性と実際の生成元比較

- `Quotient/DerivedComparisonContraction.lean`：単位が次数−1の境界である対象は既存 H⁰ で
  零となることを証明。dg Yoneda と主導来局所化でその代表加群の零性へ運ぶ。
  明示的商の `epsilonElement` と `differential_epsilonElement` から
  `quotientObject_homotopy_isZero`、`quotientRepresentable_derived_isZero` を得た。
- `Quotient/DerivedComparisonGenerators.lean`：空 path 包含の H⁰ 関手、商側 dg Yoneda、
  既存の主局所化を合成した実際の `derivedComparisonOnGenerators` を定義。
  商側の代表加群との対象計算同型、および `TriaCategory A (QuotientObject D S)` への持ち上げを構成。
  S の代表対象を殺すことと、この像が商側 tria 全体を三角生成することを証明した。
  H⁰(D) 自体からの本質的全射性は主張しない。
- この単位の零性と生成性には局所 K-flat 仮定を置かない。後続の Verdier 商上の
  完全忠実性で仮定を使う。U15e 全体・U17b は引き続き未完。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.QuotientDerivedContraction` 成功。
  主要11宣言の公理監査は標準3公理のみ。新規 sorry・axiom・引用なし。
- project import 依存372ファイルを走査し、dg 圏分解の `Resolution/`、
  `Derived/KFlatBimodule*`、`Derived/Bimodule*` への依存なし。
- ルートには他チャットの4行の import が混在しているため、この単位では編集・コミットしない。
  正本の参照一行も並行変更と混在しており、引き続き専用記録と対象ファイルだけをコミットする。
- U15e1 のコミット：`60ad82cd`（4ファイル。直後の `git show --stat HEAD` で確認済み）。

### U15e3：導来制限の本質像の必要条件

- `Quotient/DerivedComparisonRestriction.lean`：商の任意の右 dg 加群 M について、
  全ての b∈S で M(b) が acyclic であることを証明。opposite 側も同じ ε の境界式を使い、
  M の H⁰ 関手、既存の複体 H⁰ 比較、通常ホモロジー関手の順に零性を運ぶ。
- 既存の `dgDerivedRestriction` は dg 関手に沿う対象ごとの制限であり、dg 圏の分解を使わない。
  この API と既存の局所化因子化を読み取り専用で使い、導来制限の像における
  b 上の全次数ホモロジー消滅を `quotientDerivedRestriction_homology_isZero` で証明。
- 代表加群による既存 Hom 計算から、S の代表対象から導来制限の像への射は零だけと示した。
  必要条件の証明であり、局所 K-flat 仮定下の逆向きの本質像判定や完全忠実性の代用とはしない。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.QuotientDerivedRestriction` 成功。
  主要5宣言の公理監査は標準3公理のみ。新規 sorry・axiom・引用なし。
- project import 依存359ファイルを走査し、dg 圏分解の `Resolution/`、
  `Derived/KFlatBimodule*`、`Derived/Bimodule*` への依存なし。
- U15e2 のコミット：`e4b0e0ba`（自分の4ファイルだけであることを `git show --stat HEAD` で確認）。
- 残部：tria(D) 全体への比較の延長、Verdier 分母の像と path 長 filtration の比較、
  局所 K-flat 下の完全忠実性・本質的全射、U17b の perfect/Karoubi 比較。
  目的全体は継続中であり、DG-DR は採用していない。

### U15e4：tria 全体への実際の比較関手と tria(S) の零性

- `Quotient/DerivedComparisonCells.lean`：shift・有限和・標準 cone を保存する
  加群上の関手に対し、finite cell の操作木に沿う像の判定を証明。
  既存の一般 dg 加群関手の cone 比較を読み取り専用で用いた。
- 既存の graph tensor と加群の射影置換による `dgDerivedExtension` を使用。
  有限 cell は既にホモトピー射影的なので、その恒等射影置換による計算同型から
  任意の有限 cell 本質像上で三角部分圏への所属を示した。dg 圏の分解は使わない。
- `Quotient/DerivedComparisonExtension.lean`：空 path 包含に沿う実際の関手
  `derivedComparisonTria : tria(D) ⥤ tria(D/S)` を全ての対象・射に定義。
  代表対象上の計算同型、tria(S) 全体の零性、代表像による商側 tria の三角生成性を証明。
- この段階では関手の三角性、Verdier 分母の反転、局所 K-flat 下の完全忠実性・
  本質的全射は未証明。生成性だけで本質的全射性とはしない。U15e・U17b 全体は未完。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.QuotientDerivedExtension`
  成功（2629 jobs）。主要9宣言の公理監査は `propext`・`Classical.choice`・`Quot.sound` のみ。
  新規 sorry・axiom・引用なし。
- U15e3 のコミット：`0254e2de`（直後の `git show --stat HEAD` で自分の3ファイルのみと確認）。
- ルートの先行する並行差分が解消していることを確認し、自分の比較拡張・制限の import 2行を追加。
  正本の参照一行は既存記録どおりとし、追加変更しない。
- project import 依存422ファイルを走査し、`Resolution/`、`Derived/KFlatBimodule*`、
  `Derived/Bimodule*` への依存なし。標準加群解像度と dg 圏解像度は区別する。

### U15e5：三角比較の構成と指定 Verdier 商への因子化

- `Verdier/FiniteCellHomotopy.lean`：K(D) 内の finite cell 本質像を三角部分圏とし、
  その主導来局所化から tria(D) への三角同値 `homotopyFiniteCellTriaEquivalence` を構成。
  finite cell の射影性による局所化 Hom 全単射を用い、retract は加えていない。
- `Quotient/DerivedComparisonTriangulated.lean`：この三角モデルで graph tensor を使い、
  実際の三角関手 `quotientTriaFunctor : tria(D) ⥤ tria(D/S)` を構成。
  整合的整数 shift、標準代表対象上の計算同型、tria(S) の零性を証明。
- Verdier 分母の反転を証明し、U17a の指定局所化そのものからの
  `quotientVerdierComparison : TriaQuotient A D S ⥤ TriaCategory A (QuotientObject D S)`
  と因子化自然同型を構成。比較関手の三角性と因子化同型の shift 整合性も証明。
- この関手が充満なら、本質像の三角閉性と代表生成性から本質的全射性が従うことを証明。
  充満性は仮定付き補題の前提として明示しており、局所 K-flat から既に従ったとはしない。
- U15e4 の `derivedComparisonTria` は主導来射影置換による補助関手として保持。
  今後の Verdier 比較に使う関手は、三角構造を固定した `quotientVerdierComparison`。
  これら二つの補助的な構成間の自然比較は、この単位では主張していない。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.QuotientDerivedTriangulated`
  成功（2631 jobs）。主要16宣言の公理監査は標準3公理のみ。
  project import 依存424ファイルに、禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。既存の Derived/・Quotient/・Endomorphism/ は編集していない。
- U15e4 のコミット：`85c45d3a`（自分の5ファイルのみと直後に確認）。
- 残部：片側局所 K-flat 仮定から上記の実際の比較の完全忠実性を示すこと。
  path 長 filtration と Verdier 分母を通じる Hom 比較が必要。U17b の完備化比較も未完。

### U15e6：片側局所 K-flat 性からの path 係数の擬同型保存

- `Quotient/DerivedComparisonPathFlatness.lean`：入る側の Hom が K-flat なら S を終点とする
  全内部 path 項が K-flat、出る側なら S を始点とする全内部 path 項が K-flat と証明。
- path を前方係数 `pathPrefixWeight w x b` と末尾 Hom(b,y) に分ける
  `termSnocWeightIso` を tensor 結合子だけで構成。word の添字は変更しない。
  後方係数 `pathSuffixWeight w b y` は先頭 Hom(x,b) を除いた残りとして定義。
- Drinfeld の各片側仮定から対応する係数の K-flat 性を証明し、係数との tensor が
  任意の非有界な擬同型を保つことを示した。残した先頭・末尾因子の平坦性は要求しない。
  前方係数と非有界 acyclic 複体の tensor の acyclic 性も直接公開。
- これらは内部微分の path 項についての宣言。ε 消去を含む最終微分の長さ filtration、
  随伴次数部分と Verdier 分母の Hom 比較はまだ構成していない。
- M9 の商を取る前の次数零・平坦 Hom からは、既存の `allHomKFlat_of_flat_zero` と
  `allHomKFlat_into` / `allHomKFlat_outOf` で両方向の必要条件を供給できる。
  商を取った後の非正次数性だけを K-flat 性の根拠にはしない。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.QuotientPathFlatness`
  成功（2273 jobs）。主要8宣言の公理監査は標準3公理のみ。
  project import 依存113ファイルに、禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。U15e・U17b 全体は未完であり、DG-DR は採用していない。
- U15e5 のコミット：`c311d153`（自分の5ファイルのみと直後に確認）。
- ルートの path 係数 import は `git add -p` で自分の一行だけを選択したが、
  別チャットの未 stage import が同居したため、パス指定コミットへの混入を避けるべく
  自分の cached patch だけを逆適用して部分 stage を解除。ルートは今回のコミットから除外し、
  import 一行は working tree に残す。他チャットの hunk と index には触れていない。

### U15e7：最終微分の長さ filtration・零段・逐次余極限

- `Quotient/DerivedComparisonFiltration.lean`：長さ n 以下の全 path の各次数の像の和を
  `lengthSubmodule` と定義。ε 消去の成分を短い path への有限和と書き、
  消去作用素が filtration を一段下げること、最終微分 d+ε が各段階を保つことを証明。
  実際の部分複体 `lengthComplex`、単射な包含、段階間の chain map と合成則を構成。
- 各次数で全段階の和が Hom 全体であることを `lengthSubmodule_exhaustive` で証明。
  全 path 直和の余極限普遍性を用い、基礎環上の平坦性や複体の有界性は置かない。
- `Quotient/DerivedComparisonFiltrationZero.lean`：空 path への内部射影により元の Hom の
  次数ごとの包含が単射であると証明。零段の像を計算し、元の Hom 複体との実際の
  `lengthZeroIso` を構成。零段から最終 Hom への合成が `originalHomInclusion` と一致する。
- `Quotient/DerivedComparisonFiltrationColimit.lean`：長さ部分複体を ℕ 上の図式とし、
  各次数の元が有限の段階に属することから underlying Type の filtered colimit を検証。
  加群の忘却関手による反映と複体の評価による余極限判定で、
  `colimit (lengthDiagram ...) ≅ quotientHom ...` を構成し、包含との式も証明。
- 対象ビルド：`lake build` に `Checks.QuotientFiltration`・`Checks.QuotientFiltrationZero`・
  `Checks.QuotientFiltrationColimit` の3対象（いずれも完全なモジュール名）を指定して成功（1876 jobs）。
  主要23宣言の公理監査は標準3公理のみ。project import 依存は86・87・87ファイルで、
  禁止された dg 圏分解系への依存なし。新規 sorry・axiom・引用なし。
- カーネル検証で重かった制限写像の可換性は、一般の線形写像についての非公開補題に切り出し、
  検証上限を増やさずに解消した。既存ファイルは読み取り専用で使用。
- 原典 Drinfeld §8.2–8.4 を再確認。今回の厳密な ℕ 図式は path 長 filtration の図式であり、
  Verdier 分母を添字とする K(A) 内の図式とは別である。後者に対する K-flat tensor の
  ホモロジー余極限消滅（§8.4）を、厳密な複体図式の AB5 だけで代用しない。
- 残部：正の随伴次数部分を固定長 path 直和と同定し、片側 K-flat 係数を使って Verdier 分母上の
  Hom 比較を証明すること。これによる完全忠実性と U17b の完備化比較は引き続き未完。
- U15e6 のコミット：`868beacb`（自分の3ファイルのみと直後に確認）。
  ルートには他チャットの import が引き続き混在しているため、今回も編集・コミットしない。

### U15e8：正の随伴次数部分の固定長 path 計算

- `Quotient/DerivedComparisonGradedProjection.lean`：指定された word 部分集合の直和、
  全内部 path 直和への包含、その分裂射影を構成。固定長 n+1 への射影は第 n 段階を消す。
  ε 消去もその射影の下で零になるため、最終微分を持つ `lengthComplex (n+1)` から
  内部微分だけを持つ `fixedLengthHom (n+1)` への実際の chain map を構成。
- `Quotient/DerivedComparisonGraded.lean`：内部微分の cutoff 射影を使い、射影の核が
  第 n 段階の像に一致することと各次数での全射性を証明。次数ごとの加群 cokernel 計算を
  評価関手による余極限判定へ運び、複体としての cokernel 普遍性を証明。
- `lengthGradedIso` は
  `cokernel (lengthMap ... (Nat.le_succ n)) ≅ fixedLengthHom ... (n+1)` という実際の同型。
  `lengthGradedIso_π` は cokernel 射影との整合式である。
  同じ写像からの複体の短完全列も `lengthLayer_shortExact` で証明した。
- 対象ビルド：`Checks.QuotientGradedProjection`（1869 jobs）、`Checks.QuotientGraded`
  （1872 jobs）をそれぞれ完全なモジュール名で指定して成功。主要14宣言の公理監査は標準3公理のみ。
  project import 依存87・88ファイルに、禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。既存の他担当ファイルは編集していない。
- 係数の片側 K-flat 性はまだこの同型の仮定に不要。次段階は、この固定長直和を前方係数と
  Hom(b,−) の tensor に分解し、Verdier 分母での Hom ホモロジー余極限消滅へつなぐこと。
  完全忠実性と U17b 全体は引き続き未完。
- U15e7 のコミット：`266ef182`（自分の7ファイルのみと直後に確認）。

### U15e9：随伴次数部分の tensor 表示と局所直交条件からの消滅

- `Quotient/DerivedComparisonGradedTensor.lean`：長さ n+1 の word を
  「先頭 b と長さ n の残り」または「末尾 b と長さ n の残り」で添字付けする明示的同値を構成。
  既存の全次数 tensor の結合子による同型を使い、固定長直和とその cokernel 表示を
  `∐ (b,w), pathPrefixWeight w x b ⊗ Hom(b,y)` および
  `∐ (b,w), Hom(x,b) ⊗ pathSuffixWeight w b y` という複体の同型へ移した。
- 添字族の small 性から、Shrink による同値で加群余積の exact 性を供給。
  u-small な非有界 acyclic 複体の直和が acyclic であることを証明し、
  元の word の添字を変えずに利用する補題 `pathCoproduct_acyclic` として公開。
- 入る側の K-flat 仮定と全 Hom(b,y) の acyclic 性、または出る側の K-flat 仮定と
  全 Hom(x,b) の acyclic 性から、全ての正の固定長層が acyclic と証明。
  これは実際の dg 圏の対象 x,y に対する消滅であり、まだ Verdier 分母上の余極限の消滅ではない。
- 対象ビルド：`lake build SerrePositivity.DifferentialGraded.Checks.QuotientGradedTensor`
  成功（2316 jobs）。主要9宣言の公理監査は標準3公理のみ。
  project import 依存154ファイルに、禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。既存の他担当ファイルは編集していない。
- U15e8 のコミット：`b2674f98`（自分の5ファイルのみと直後に確認）。
  U15e の完全忠実性と U17b 全体は引き続き未完。

### U15e10：厳密余極限の擬同型保存と直交対象上の Hom 比較

- `Quotient/DerivedComparisonColimitQuasiIso.lean`：厳密な複体図式の自然変換を関手圏内の
  複体の射へ転置し、評価による擬同型判定と exact な colim 関手による保存を使う。
  次数ごとの余極限で作った複体との比較同型とその自然性を証明し、指定された
  `colimMap` 自身が擬同型になることを `complex_colimMap_quasiIso` で示した。
- この補題は **厳密な複体図式と厳密自然変換** に対するもの。
  Drinfeld §8.4 のホモトピー圏内だけの図式の主張を仮定・引用したものではない。
- `Quotient/DerivedComparisonLocalHom.lean`：短完全列の第三項が acyclic なら第一射が
  擬同型となることを長完全列から証明。全ての正の固定長層が acyclic なら、零段から各長さ段階への
  射は擬同型となる。これらを厳密な ℕ 図式の自然変換にし、上記補題と長さ余極限同型により
  `originalHomInclusion : Hom_D(x,y) ⟶ quotientHom ... x y` 自身の擬同型性を証明。
- その仮定を、入る側 K-flat と全 Hom(b,y) の acyclic 性、または出る側 K-flat と全 Hom(x,b) の
  acyclic 性から供給する `originalHomInclusion_quasiIso_into` / `_outOf` を公開。
  実際の D の対象 x,y に対する補題であり、任意の x,y 上の無条件な Hom 擬同型とはしない。
- 対象ビルド：`Checks.QuotientColimitQuasiIso` と `Checks.QuotientLocalHom` をそれぞれ
  完全なモジュール名で指定して成功。後者は2323 jobs。主要9宣言の公理監査は標準3公理のみ。
  project import 依存5・158ファイルに、禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。ルートおよび他担当の既存ファイルは編集していない。
- U15e9 のコミット：`83b0a72a`（自分の3ファイルのみと直後に確認）。
- 残部：この Hom 計算を tria の対象および Verdier 分母の比較へ延長し、実際の
  `quotientVerdierComparison` の完全忠実性を証明すること。U17b の完備化比較も未完。

### U15e11：長さ部分複体の全次数作用

- `Quotient/DerivedComparisonFiltrationAction.lean`：固定した word 部分集合の直和への
  先頭 Hom 作用を構成。その包含・射影と作用の可換性を、各 path の包含で検証した。
  cutoff も作用と可換になるので、元の Hom の任意の斉次次数について、内部作用と
  最終微分についての作用が長さ部分加群を保つことを証明した。
- `Quotient/DerivedComparisonLengthAction.lean`：双次数の作用を部分加群へ制限し、
  最終微分の Leibniz 則で非有界 tensor から `lengthComplex` への実際の chain map
  `lengthPrepend` を構成。包含との整合式 `lengthPrepend_inclusion` と、
  長さを増やす写像との整合式 `lengthPrepend_map` を証明した。
- ここまでの構成は underived であり、K-flat 仮定は不要。右 dg 加群の構成に必要な
  全次数の作用を供給するが、まだ豊穣関手の単位・合成法則を備えた加群構成ではない。
  その加群構成と、正の層が S の代表加群から生成されることを介して、比較の完全忠実性へ進む。
- 対象ビルド：`Checks.QuotientFiltrationAction`（1879 jobs）および
  `Checks.QuotientLengthAction`（1880 jobs）を完全なモジュール名で指定して成功。
  主要12宣言の公理監査は標準3公理のみ。project import 依存95・96ファイルに
  禁止された dg 圏分解系への依存なし。新規 sorry・axiom・引用なし。
- U15e10 のコミット：`680c2331`（自分の5ファイルのみと直後に確認）。
  U15e の完全忠実性と U17b 全体は引き続き未完。

### U15e12：右 dg 加群としての長さ filtration と余極限

- `Quotient/DerivedComparisonLengthModule.lean`：先頭作用が商の合成を元の Hom に
  制限したものと等しいことを証明し、商の代表加群の制限との作用比較を構成。
  `lengthModuleMap` と包含との全次数可換式を利用して、単位・合成法則を証明した。
  `lengthModule` は豊穣関手としての実際の右 dg 加群である。
- 包含 `lengthModuleInclusion` は全次数自然な実際の加群射であり、mono。
  長さを増やす `lengthModuleTransition` とその包含整合式を証明し、
  右 dg 加群圏内の厳密な ℕ 図式 `lengthModuleDiagram` と cocone を構成した。
- `Quotient/DerivedComparisonModuleColimit.lean`：評価後の図式・cocone を既存の
  Hom の長さ図式・cocone と比較する同型を構成。評価による余極限反映を使い、
  商の制限代表加群がこの加群図式の真の余極限であることを証明。
  `lengthModuleColimitIso` と、その全ての余極限包含に対する整合式を公開した。
- ここまでの加群構成も underived で、K-flat 仮定不要。残る主要段階は、
  正の層を S 上の自由加群で表し、片側 K-flat 仮定の下で局所化の核に入れること、
  そして `quotientVerdierComparison` の完全忠実性を導くこと。U17b 全体も未完。
- 対象ビルド：`Checks.QuotientLengthModule`（1932 jobs）、
  `Checks.QuotientModuleColimit`（1940 jobs）成功。主要19宣言の公理監査は標準3公理のみ。
  project import 依存145・149ファイルに禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。既存の他担当ファイルは編集していない。
- ルートは他担当の CLMST import と同居しているため、今回のコミット対象から除外。
  自分の以前の `DerivedComparisonPathFlatness` import は引き続き作業ツリー内に残っている。
- U15e11 のコミット：`637a2212`（自分の5ファイルのみと直後に確認）。
