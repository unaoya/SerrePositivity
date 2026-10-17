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

## 追加担当：局所 K-flat 版 U15e・U17b（完了、U16 の自然性は後続）

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

### U15e13：固定長 path の自由右加群表示

- `Quotient/DerivedComparisonPathModule.lean`：既存の全次数 `tensorRightHom` の単位・合成を
  豊穣関手としてまとめ、各内部 path 項を右 dg 加群 `pathModule` にした。
  値と従来の `term` の明示的な複体同型、および先頭 Hom 作用との整合式を証明。
  正の word `b :: w` の加群は、符号付き交換によって
  `(freeAt b.val).obj (pathSuffixWeight w b z)` と実際の加群圏で同型になる。
  この交換は全次数の Hom 作用と可換であり、閉零射だけの比較ではない。
- `Quotient/DerivedComparisonGradedModule.lean`：任意の word 部分集合について、path 加群の
  直和 `selectedPathModule` を構成。評価と従来の `selectedHom` の同型を作り、
  全ての path 包含との整合性、および全次数の先頭作用との可換性を証明した。
  `fixedLengthModuleFreeIso` は、長さ n+1 の加群と
  `∐ (b,w : S × LengthWord S n), (freeAt b.val).obj (pathSuffixWeight w b z)` の同型。
- ここまでの表示は underived で K-flat 仮定不要。まだ `lengthModuleTransition` の
  加群圏での cokernel とこの固定長加群を同定したものではない。
  次段階は層射影を全次数自然な加群射にして cokernel と同定し、片側 K-flat 仮定を使って
  この自由加群表示から導来圏での S による生成を示すこと。
  U15e の完全忠実性と U17b 全体は引き続き未完。
- 対象ビルド：`Checks.QuotientPathModule` と `Checks.QuotientGradedModule` の単独指定、
  最終的には両方を指定した `lake build` 成功（2329 jobs）。主要12宣言の公理監査は標準3公理のみ。
  project import 依存126・166ファイルに禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。ルートおよび他担当の既存ファイルは編集していない。
- U15e12 のコミット：`3a215fcf`（自分の5ファイルのみと直後に確認）。

### U15e14：加群 filtration の cokernel と導来三角形

- `Quotient/DerivedComparisonLayerModule.lean`：固定長への層射影が全次数の先頭作用と
  可換であることを、内部射影の可換式から証明。評価同型を経由して、
  `lengthLayerModuleProjection` を実際の全次数自然な右 dg 加群射として構成した。
  相隣る長さ部分加群の包含との合成は零。
- 評価後の cokernel cocone を既存の複体の cokernel と三成分の同型で比較し、
  評価による余極限反映を適用した。`lengthLayerModule_isColimit` は加群圏での真の普遍性。
  `lengthModuleGradedIso` と cokernel 射影との整合式、および前段の自由加群表示を合成した
  `lengthModuleGradedFreeIso` を公開。従って随伴次数部分の自由加群表示は、値ごとの同型だけでなく
  加群圏内の実際の cokernel からの同型になった。
- `Quotient/DerivedComparisonLayerTriangle.lean`：評価後の列の短完全性を証明。
  包含の実際の加群 cone から層への延長 `lengthLayerConeDesc` を作り、
  複体の短完全列に対する cone 比較から objectwise 擬同型であることを示した。
  これを導来圏で反転し、相隣る長さ部分加群と固定長 path 加群を結ぶ
  `lengthLayerDerivedTriangle` が distinguished であることを証明した。
- 以上に K-flat 仮定は不要。残部は、片側 K-flat 仮定の下で自由加群表示の導来像が
  S の代表加群から生成されること、長さの余極限へその主張を移すこと、
  そこから `quotientVerdierComparison` の完全忠実性を導くこと。U17b 全体も未完。
- 対象ビルド：`Checks.QuotientLayerModule`（2372 jobs）、
  `Checks.QuotientLayerTriangle`（2456 jobs）成功。主要17宣言の公理監査は標準3公理のみ。
  project import 依存210・275ファイルに禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。ルートおよび他担当の既存ファイルは編集していない。
- U15e13 のコミット：`8be670fe`（自分の5ファイルのみと直後に確認）。

### U15e15：零段階の代表加群同型と商への比較射

- `Quotient/DerivedComparisonZeroModule.lean`：複体としての `lengthZeroMap` を、
  全次数自然な実際の加群射 `lengthZeroModuleMap` へ持ち上げた。
  作用の可換性は、商の制限代表加群への次数ごとの単射な包含を通じて検証している。
  評価による同型反映から、元の代表加群と零段階の加群同型 `lengthZeroModuleIso` を構成。
- 零段階の包含との合成が、実際の dg 商包含の Hom 写像による
  `representableRestrictionMap` と等しいことを `lengthZeroModuleMap_inclusion` で証明した。
  従って長さ filtration の始点・終点・比較射が加群圏内で接続された。
- 対象ビルド `Checks.QuotientZeroModule` 成功（単独2570 jobs、最後の再検証は併合ビルド内）。
  主要4宣言の公理監査は標準3公理のみ。project import 依存381ファイルに禁止分解系なし。
  新規 sorry・axiom・引用なし。他担当およびルートのファイルは編集していない。
  この同型には K-flat 仮定は不要。U15e の完全忠実性と U17b 全体は引き続き未完。
- U15e14 のコミット：`0deb4cca`（自分の5ファイルのみと直後に確認）。

### U15e16：代表加群から全導来対象への localizing 帰納法

- `Verdier/DerivedGeneratorInduction.lean`：同型・三角形・u-small 余積に閉じて全代表加群を
  含む導来対象の性質 P が、全ての導来対象で成立することを証明した。
  U13d で受け入れた通常の dg 加群の標準解像度を再利用し、free sphere の余積、
  各解像度段階、逐次余極限の cone 表示、標準解像度の擬同型の順に帰納する。
  dg 圏の分解や比較定理の引用は使わない。
- `moduleDerived_generatorInduction` はこの主張を任意の対象性質 P について公開する。
  `moduleDerived_functor_generatorInduction` は、三角形・u-small 余積を保つ導来関手 F の
  像の性質も、F による全代表加群の像上で検証すればよいという形で公開する。
  関手の三角性・余積保存と P の閉性は、この一般補題の明示的な仮定である。
- これは任意の D の全代表加群に対する生成の帰納法。まだ、商の正の層を構成する
  `(freeAt b).obj K` の導来像が S の代表加群で生成されること自体を証明したものではない。
  次段階で、片側 K-flat 仮定の下での自由加群の導来比較とこの帰納法を接続する必要がある。
  U15e の完全忠実性と U17b 全体は引き続き未完。
- 対象ビルド `Checks.DerivedGeneratorInduction` 成功（2491 jobs）。主要6宣言の公理監査は
  標準3公理のみ。project import 依存297ファイルに禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。ルートおよび他担当の既存ファイルは編集していない。
- U15e15 のコミット：`4f129b47`（自分の3ファイルのみと直後に確認）。

### U15e17：係数 K-flat 自由加群の導来計算と正の path 項の局所生成

- `Quotient/DerivedComparisonFreeExtension.lean`：一対象環 A から b への dg 関手を構成。
  普通の加群の延長–制限随伴と一対象加群・複体の同値を合成し、随伴の一意性によって
  一対象環からの underived 延長と `freeAt b` の自然同型を作った。
- 相対 K-flat 加群間の擬同型について、graph 延長は各評価でそれを保つ。
  射影置換の相対 K-flat 性とこの保存を使い、`relativeKFlatExtensionComputation` で
  相対 K-flat 加群の導来延長を underived 延長と比較した。
  `derivedFreeAtKFlatIso` は、K-flat 係数 K の自由加群を一対象環からの導来延長で計算する実際の同型。
- `Quotient/DerivedComparisonFreeGeneration.lean`：導来延長の三角性・左随伴としての余積保存と
  前段の生成帰納法を接続した。S 内の b と K-flat 複体 K について、
  `(freeAt b).obj K` の導来像が `moduleFiniteCellFactorTarget ... S` を満たすことを証明。
  これは compact 対象からの全ての射が S 上の有限 cell 対象を経由するという具体的な性質である。
- 一対象環上の普通の射影置換を評価し、任意の非有界複体の K-flat 置換も構成。
  Hom(−,b) が K-flat なら `freeAt b` はその係数擬同型を保つため、入る側の仮定では
  自由加群の係数 K を任意にできる。出る側の仮定では既存の後方係数の K-flat 性を使う。
  `positivePath_finiteCellFactorTarget` は両向きをまとめ、全ての個々の正の path 項に適用する。
- M9 接続：`positivePath_finiteCellFactorTarget_of_flat_zero` は、元の dg 圏の Hom が
  次数零に集中し、その次数零加群が平坦という入力から直接同じ有限因子分解性を供給する。
  商の Hom の非正次数性から K-flat 性を推論したものではない。
- 対象ビルド `Checks.QuotientFreeExtension`（2533 jobs）、`Checks.QuotientFreeGeneration`
  （2621 jobs）成功。主要14宣言の公理監査は標準3公理のみ。
  project import 依存344・420ファイルに禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。ルートおよび他担当の既存ファイルは編集していない。
- 残部：個々の path 項の性質を、固定長直和の導来像と長さ余極限に運ぶこと、
  そこから商への代表加群比較の cone の有限因子分解性と実際の Verdier 比較の完全忠実性を示すこと。
  U17b 全体も未完。U15e16 のコミットは `a4d21297`（自分の3ファイルのみと直後に確認）。

### U15e18：導来局所化の余積保存と有限長比較 cone の局所生成

- `Verdier/DerivedCoproductComparison.lean`：厳密な加群図式の自然変換が objectwise 擬同型なら、
  評価先の加群余極限が exact である形の余極限でも擬同型になることを証明。
  u-small な加群の直和写像にも適用した。
- 任意の加群族を項ごとに普通の射影置換へ置き換え、置換間の余積比較と上記の擬同型保存を使って、
  局所化した元の余積包含が導来圏の真の余積になることを証明。
  `moduleDerivedCofanIsColimit`、`moduleDerivedCoproductIso` と全包含に対する整合式、
  `moduleToDerived_preservesCoproducts` を公開。加群族そのものに射影性は仮定しない。
- `Quotient/DerivedComparisonLayerGeneration.lean`：受け入れ済みの有限因子分解性の余積閉性を
  underived 加群余積の導来像へ運んだ。逐次余極限についても、標準の逐次余極限の cone 表示、
  その objectwise 擬同型、および cone 三角形を使って同じ閉性を証明した。
- 局所 K-flat 仮定から個々の正の path 項の生成性を全ての正の固定長層へ運び、
  相隣る長さ段階間の比較 cone の有限因子分解性を証明。
  distinguished triangle による `trW` 判定とその合成閉性を使い、零段階から任意の有限長段階への
  比較が `trW` に入ることと、その実際の加群 cone の有限因子分解性まで証明した。
- 対象ビルド `Checks.DerivedCoproductComparison`（2201 jobs）、
  `Checks.QuotientLayerGeneration`（2707 jobs）成功。主要13宣言の公理監査は標準3公理のみ。
  project import 依存146・506ファイルに禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。他担当およびルートの既存ファイルは編集していない。
- 残部：有限長比較 cone の厳密な図式の余極限を、商の制限代表加群全体への比較 cone と
  同定すること。その有限因子分解性から実際の Verdier 比較の完全忠実性を導くこと。
  U17b 全体も引き続き未完。
- U15e17 のコミット：`d60bd909`（自分の5ファイルのみと指定 SHA でも確認）。


### U15e19：有限長比較 cone の余極限と代表加群比較の cone

- `Quotient/DerivedComparisonConeDiagram.lean`：零段階から各有限長段階への射を
  arrow 圏の厳密な図式にし、加群 cone 関手で比較 cone の逐次図式を構成した。
  零段階から商全体への cone を頂点とする具体的な cocone も構成。
- `Quotient/DerivedComparisonConeColimit.lean`：各評価・各次数で、cone 写像の
  二成分表示から単射性と有限段階からの全射性を証明した。後者では商 Hom の
  任意の元が有限長の path 和であることを使い、filtered colimit の判定を適用。
  その結果を複体・全次数自然な加群の余極限性へ持ち上げた。
- `Quotient/DerivedComparisonUnitCone.lean`：この厳密な余極限と前段の逐次余極限閉性から、
  零段階から商全体への比較 cone の有限因子分解性を証明した。零段階の代表加群同型を
  arrow 同型・実際の加群 cone 同型に運び、元の代表加群から商の制限代表加群への
  `representableRestrictionMap` の cone に同じ性質を得た。
  `quotientRepresentableComparison_trW` として比較射そのものの分母条件も公開。
- 仮定は従来の `localKFlat`、すなわち全ての Hom(−,b) が K-flat、または
  全ての Hom(b,−) が K-flat（b ∈ S）のいずれかの全体的な向き。
  係数環は任意、複体は非有界で、商 Hom そのものの K-flat 性は仮定していない。
- 対象ビルド `Checks.QuotientConeDiagram`・`Checks.QuotientConeColimit`・
  `Checks.QuotientUnitCone` 成功（合同2720 jobs、追加監査対象2718 jobs）。
  主要15宣言の公理監査は標準3公理のみ。project import 依存516ファイルに
  禁止された dg 圏分解系への依存なし。新規 sorry・axiom・引用なし。
  ルート・他担当の既存ファイルは編集していない。
- 残部：この cone の有限因子分解性を実際の Verdier 比較の充満忠実性に結ぶこと。
  U17b 全体も引き続き未完。U15e18 のコミットは `6c54be24`。


### U15e20：比較 cone からの有限 cell roof と指定局所化での核の消滅

- `Quotient/DerivedComparisonFiniteRoof.lean`：指定有限 cell を経由する射に対し、
  その中間有限 cell への射を三角形に完成し、cone が指定有限 cell である分母を構成した。
  始域が tria(D) に属すれば、新しい分母の始域も tria(D) に属す。
- `finiteCellRoof_of_cone_factorTarget`：比較三角形の cone が有限因子分解性を持つ場合、
  tria(D) の対象からその第二対象への任意の射は、指定有限 cell の cone を持つ分母の後で
  第一対象への射に持ち上がる。三角形の Hom 完全性を使う直接の証明。
- 逆回転三角形を使い、比較後に零となる射は cone の逆 shift を経由し、指定有限 cell に
  因子分解することも証明した。同じ分母構成から、既に分母の後で零となる。
- 前段の実際の代表加群比較に適用した `quotientRepresentable_exists_finiteCellRoof` と、
  U17a の部分圏にそのまま値を持つ `quotientRepresentable_exists_triaRoof` を公開。
  後者の分母はまさに `(triaImage A D S).trW`。別の局所化を導入していない。
- `triaQuotient_map_eq_zero_of_representableComparison`：元の代表加群を終域とする射が
  制限代表加群への比較後に零なら、指定した `triaQuotient` で零になる。
  実際に構成した分母を局所化で可逆にして証明した。
- 対象ビルド `Checks.QuotientFiniteRoof` 成功（2748 jobs）。主要8宣言の公理監査は
  標準3公理のみ。project import 依存536ファイルに禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。他担当・ルートの既存ファイルは編集していない。
- 残部：これらの射の表示と核消滅を、商側導来 Hom と実際の `quotientVerdierComparison`
  に接続し、充満忠実性を全 tria 対象へ運ぶこと。U17b 全体も未完。
  U15e19 のコミットは `beaf1d1b`（自分の7ファイルのみと直後に確認）。


### U15e21：導来制限の全有限 cell に対する右直交性と Hom の局所化

- `Quotient/DerivedComparisonLocalObjects.lean`：導来制限の本質像は整数 shift で閉じる。
  その左直交部分圏に S の全代表加群が入ることから、生成性によって S 上の全有限 cell に
  対する右直交性を証明した。商の任意の導来加群の制限に適用し、K-flat 仮定は不要。
- `quotientDerivedRestriction_isLocal` は、指定有限 cell の cone を持つ射の前置が、
  制限の像への Hom 上で全単射であることを示す。U17a の tria 分母にもそのまま適用する。
  置換を要さない制限の計算式によって、実際の制限代表加群にも同じ局所性を得た。
- `Quotient/DerivedComparisonHomPresheaf.lean`：制限代表加群への導来 Hom の反変関手を、
  指定した `(triaQuotient A D S).op` に沿って局所化した。
  局所化上の値を元の導来 Hom と同定する同値と、元の tria の射に沿う前置との自然性を公開。
  別の Verdier 商や代替の mapping object は導入していない。
- 対象ビルド `Checks.QuotientLocalObjects`（2622 jobs）・`Checks.QuotientHomPresheaf`
  （2623 jobs）成功、警告なし。主要11宣言の公理監査は標準3公理のみ。
  project import 依存409・410ファイルに禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。既存の他担当ファイル・ルートは編集していない。
- U15e20 のコミットは `5ac8a3eb`（自分の3ファイルのみと直後に確認）。


### U15e22：指定 Verdier 商の代表対象を終域とする実際の Hom 同値

- `Quotient/DerivedComparisonRepresentableHom.lean`：指定局所化上に降りた Hom 反変関手を、
  実際の代表加群比較写像に作用させて `quotientRepresentableHomMap` を定義した。
  元の tria の射では、導来圏の射に比較写像を後置する写像そのものになる。
  元の tria の射による前置との整合性も証明。
- 局所 K-flat 仮定の下で、U15e20 の roof 表示と制限代表加群の局所性から全射性を証明。
  任意の局所化の射を右分数に表示し、その比較値が零なら射自体が零になることも証明した。
- 単射性では二つの右分数の分母を calculus of fractions によって共通化する。
  共通の始域からの元の射の差に既存の核消滅を適用し、指定局所化で等しいことを得た。
  Type 値の局所化された反変関手に、証明されていない加法性を仮定していない。
- `quotientRepresentableHomEquiv` は、任意の X ∈ tria(D) と z ∈ D に対する
  Hom(TriaQuotient, QX, Qrep(z)) ≃ Hom(D(D), X, restrict(rep(D/S,z))) の実際の同値。
  `quotientDerivedRepresentableHomEquiv` は、受け入れ済みの普通の加群の導来延長–制限随伴を
  合成し、右辺を明示的 dg 商側の Hom(Lextension(X), rep(z)) に直す。
- 対象ビルド `Checks.QuotientRepresentableHom` 成功（2756 jobs）、警告なし。
  主要8宣言の公理監査は標準3公理のみ。project import 依存541ファイルに
  禁止された dg 圏分解系への依存なし。新規 sorry・axiom・引用なし。
  他担当・ルートの既存ファイルは編集していない。
- 残部：この Hom 同値が `quotientVerdierComparison` の実際の射写像に一致することを、
  代表加群上の導来随伴の単位との整合性から確認すること。
  さらに整数 shift と三角生成性で終域を全 tria 対象へ広げ、充満忠実性と同値を得ること。
  U17b 全体も未完。U15e21 のコミットは `d000e04c`。
  直後に別チャットが HEAD を進めたため、指定 SHA で自分の5ファイルのみと確認した。


### U15e23：導来随伴で正規化した代表加群の延長同型

- `Quotient/DerivedComparisonAdjointUnit.lean`：普通の加群の標準射影置換の増強を延長し、
  `derivedExtensionUnderivedMap` を構成した。任意の underived 延長からの加群射を後置し、
  導来随伴で転置すると、元の underived 随伴での転置を導来化した射に一致する。
  射影置換の増強の可逆性と underived 随伴の自然性から直接証明した。
- 加群がホモトピー射影的なら、この比較射は同型になる。相手側 Hom の K-flat 性は不要。
  代表加群に適用し、既存の underived 代表加群同型と合成して
  `derivedExtensionRepresentableUnitIso` を構成した。
- この同型の随伴転置は、既存の `representableRestrictionMap` を導来化した射に
  制限の計算同型の逆を後置したものと、実際に等しい。
  `derivedExtensionRepresentableUnitIso_homEquiv` がこの正規化を固定する。
  dg 圏の解像度、原典の比較定理の引用、または射写像の一致の仮定は使っていない。
- 対象ビルド `Checks.QuotientAdjointUnit` 成功（2523 jobs）、警告なし。
  主要5宣言の公理監査は標準3公理のみ。禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。ルート・他担当の既存ファイルは編集していない。
- 残部：この正規化を U15e22 の Hom 同値に適用し、実際の比較関手の射写像との一致を示す。
  全 tria 対象への拡張と U17b も未完。U15e22 のコミットは `f24ecc0e`。


### U15e24：Hom 同値の正規化と実際の導来延長の因子化の射写像

- `Quotient/DerivedComparisonHomNormalization.lean`：U15e22 の Hom 同値を随伴で転置した値を
  明示的に計算した。U15e23 の正規化を使い、元の tria の射 f に対する値が、実際の
  導来延長による f の像に正規化済みの代表同型を後置したものと等しいことを証明した。
  任意の局所化の射に対して、元の tria の射による前置との整合性も公開。
- `Quotient/DerivedComparisonDerivedLift.lean`：既存の `derivedComparisonFromTria`
  （普通の加群の実際の導来延長を tria に制限した関手）の shift・三角性を付与し、
  指定した `triaQuotient` に沿う因子化 `derivedQuotientLift` と因子化同型を構成。
  これは導来加群圏に値を持つ実際の導来延長の因子化である。
- 因子化関手の射写像を因子化同型と代表同型で移すと、U15e22 の Hom 同値と一致する。
  元の射上の一致と前置の整合性を、右分数表示と分母の像の可逆性で全ての局所化の射へ広げた。
- `derivedQuotientLift_map_bijective_representable`：任意の X ∈ tria(D)、z ∈ D について、
  この因子化関手そのものの Hom(QX,Qrep(z)) 上の射写像が全単射である。
  単に別途の集合の同値が存在するという主張ではなく、実際の関手の map に関する結論。
- 対象ビルド `Checks.QuotientHomNormalization`（2760 jobs）・`Checks.QuotientDerivedLift`
  （2764 jobs）成功、警告なし。主要11宣言の公理監査は標準3公理のみ。
  project import 依存545・549ファイルに禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。他担当・ルートの既存ファイルは編集していない。
- 残部：終域の整数 shift・三角生成性から全対象への射写像の全単射性を得ること。
  有限 cell のホモトピー圏モデルから構成済みの `quotientVerdierComparison` と、
  上記の実際の導来延長の因子化との自然同型も確認する。U17b 全体は未完。
  U15e23 のコミットは `7a0b776c`（自分の3ファイルのみと直後に確認）。


### U15e25：shift・三角生成による実際の導来因子化の全対象での充満忠実性

- `Verdier/ShiftedHomComparison.lean`：関手の Hom 写像の全単射性を始点・終点の同型で移す。
  整数 shift との比較同型を持つ関手について両端を shift しても保たれることを証明し、
  任意の始域からの Hom が全単射になる終域の性質 `homComparisonTarget` の同型閉性・shift 閉性を得た。
- `Verdier/TriangulatedHomComparison.lean`：三角関手について、この性質の三角閉性を直接証明。
  単射性では逆回転三角形の像と Hom の完全性、全射性では元の三角形の像とその完全性を使う。
  零対象もこの性質を持ち、全体で厳密充満な三角部分圏になる。
- `Quotient/DerivedComparisonFullFaithful.lean`：実際の導来延長の因子化に shift・三角性を付与。
  指定局所化の本質的全射性で、代表対象を終域とする結果の始域を任意の商対象へ広げた。
  上記の性質を `triaQuotient` で引き戻し、代表生成性から全終域へ拡張した。
- `derivedQuotientLift_map_bijective` は局所 K-flat 仮定の下で、指定 Verdier 商の任意の二対象の
  間の実際の射写像が全単射であることを示す。
  `derivedQuotientLiftFullyFaithful` はその充満忠実性データを明示的な仮定付きで公開する。
- 合同対象ビルド `Checks.ShiftedHomComparison`・`Checks.TriangulatedHomComparison`・
  `Checks.QuotientFullFaithful` 成功（2769 jobs）、警告なし。
  主要14宣言の公理監査は標準3公理のみ。project import 依存1・2・552ファイルに
  禁止された dg 圏分解系への依存なし。新規 sorry・axiom・引用なし。
  ルート・他担当の既存ファイルは編集していない。
- 残部：商側 tria に値域を制限した同値、既存のホモトピー有限 cell モデルによる
  `quotientVerdierComparison` との自然同型、および U17b。
  U15e24 のコミットは `2ef7745f`（自分の5ファイルのみと直後に確認）。


### U15e26：局所 K-flat 版の指定 Verdier 商と明示的 dg 商の tria の実際の同値

- `Quotient/DerivedComparisonEquivalence.lean`：導来延長の因子化の値が商側の有限 cell
  本質像に属することを、指定局所化の本質的全射性と因子化同型から証明した。
  値域を `TriaCategory A (QuotientObject D S)` に制限した `localQuotientTriaFunctor` は
  実際の導来延長から構成され、整数 shift と三角構造を保つ。
- `localQuotientTriaFullyFaithful` は前段の全対象での充満忠実性を充満部分圏へ制限する。
  代表対象の像を正規化済みの代表同型で計算し、充満な三角関手の本質像の三角閉性と
  商側の代表生成性から本質的全射性を証明した。
- `localQuotientTriaEquivalence`：局所 K-flat 仮定を明示的に受け取り、
  指定した `TriaQuotient A D S` と明示的 dg 商の `TriaCategory` の実際の同値を構成した。
  原典の比較定理の引用や dg 圏の解像度による代替は使っていない。
- M9 用の `localQuotientTriaEquivalence_of_flat_zero` も公開。
  商を取る前の全 Hom が次数零に集中し、次数零加群が平坦であることから K-flat 性を供給する。
  非零次数の平坦性を別途要求せず、商側 Hom の非正次数性から K-flat 性を推論していない。
- 対象ビルド `Checks.QuotientLocalEquivalence` 成功（2768 jobs）、警告なし。
  主要7宣言の公理監査は標準3公理のみ。禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。他担当・ルートの既存ファイルは編集していない。
- 残部：既存のホモトピー有限 cell モデルの `quotientVerdierComparison` との自然同型と、
  U17b の perfect enhancement・Karoubi 比較。U15e25 のコミットは `dc80a204`。


### U17b1：局所 K-flat 版の perfect enhancement と指定完備 Verdier 商の三角同値

- `Verdier/KaroubiTransport.lean`：既存の Karoubi 関手延長を使って圏同値を完備化する。
  完備化した関手の本質的全射性は、形式的直和因子の標準 retract を元の圏の同値で移し、
  既存の `karoubiExtension_mem_essImage` に適用して証明した。完備化の代替構成は作っていない。
- `Quotient/DerivedComparisonPerfect.lean`：U15e26 の同値を Karoubi 完備化した
  `localCompletedQuotientEquivalence` を構成。既存の有限 cell Karoubi–Perf 同値と
  perfect dg 加群の H⁰–Perf 同値を合成して、
  `localPerfectQuotientEquivalence` : H⁰(Perf_dg(D/S)) ≌ CompletedTriaQuotient A D S を得た。
  `localSmallPerfectQuotientEquivalence` は既存の小さい dg 代表系を使った同じ比較。
- 両 perfect 比較は整数 shift に整合する三角同値であることも明示的に証明した。
  任意の係数環、非有界加群、元の局所 K-flat 仮定を保持し、dg 圏の解像度には依存しない。
- `localPerfectKaroubiFirstEquivalence` と `localPerfectPaperSequenceComparison` によって、
  U17a の `triaKaroubiOrderEquivalence`・`triaKaroubiComparison` に実際に接続した。
  後者は既存の順序交換比較を perfect enhancement への逆比較に後置する自然同型であり、
  別の零対象クラスや異なる完備 Verdier 商を使っていない。
- M9 入力を受け取る `localPerfectQuotientEquivalence_of_flat_zero` も公開。
  元の dg 圏の次数零に集中した平坦 Hom から必要な K-flat 性を供給できる。
  商側 Hom の非正次数性だけでは供給しない。
- 対象ビルド `Checks.KaroubiTransport`（1000 jobs）・`Checks.QuotientLocalPerfect`
  （2783 jobs）成功、警告なし。主要12宣言の公理監査は標準3公理のみ。
  project import 依存2・568ファイルに禁止された dg 圏分解系への依存なし。
  新規 sorry・axiom・引用なし。他担当・ルートの既存ファイルは編集していない。
- U16 の Morita 比較の関手・自然変換に関する自然性は、この点ごとの同値の構成には使わず後回し。
  その入力の型と可換図式を追加する段階で接続する。既存のホモトピー有限 cell モデルの
  `quotientVerdierComparison` と導来延長に基づく今回の比較との自然同型も残る。
  これらの接続を未検証のまま全目標完了とはしない。
  U15e26 のコミットは `4ff8cb8b`（自分の3ファイルのみと直後に確認）。


### U15e27：既存の指定比較関手との自然同型と最終受入

- `Quotient/DerivedComparisonExtensionCoherence.lean`：普通の加群上の
  `derivedExtensionUnderivedMap` の自然性を、underived と derived の随伴による転置の整合性から証明。
  自然変換をホモトピー商へ降ろし、有限 cell 上ではホモトピー射影性から各成分が可逆になる。
  `finiteCellHomotopyDerivedExtensionIso` は、その部分圏上の二つの延長計算の実際の自然同型。
- `Quotient/DerivedComparisonCanonical.lean`：有限 cell のホモトピー圏と tria の既存の同値で
  上の自然同型を運び、商側の充満部分圏へ制限した。
  指定 Verdier 局所化の前置の完全忠実性で因子化後にも降ろし、
  `quotientComparisonModelsIso` : localQuotientTriaFunctor ≅ quotientVerdierComparison を得た。
- `quotientVerdierComparisonFullyFaithful` は、局所 K-flat 仮定から既存の指定関手そのものの
  充満忠実性を証明する。`quotientVerdierLocalEquivalence` は、この指定関手を関手部分とする
  実際の圏同値。整数 shift と三角構造にも整合する。
  仮定として充満忠実性を受け取る経路や、代表対象上だけの集合の同値で置き換えていない。
- 合同対象ビルド `Checks.QuotientExtensionCoherence`・`Checks.QuotientCanonicalComparison`・
  `Checks.QuotientLocalPerfect` 成功（2789 jobs）、警告なし。
  今回の主要13宣言と perfect 比較の10宣言の公理監査は全て標準3公理のみ。
  今回の project import 依存355・557ファイル、および perfect 比較の568ファイルに
  禁止された dg 圏分解系への依存なし。担当の DerivedComparison・Verdier ソースを再走査し、
  新規 sorry・axiom がないことも確認。比較定理 DG-DR を含め、引用採用は0件。
  他担当・ルート・README・Stage の既存ファイルは今回編集していない。
- U17b1 のコミットは `9ea5e9ca`（自分の5ファイルのみと直後に確認）。

### 局所 K-flat 版 U15e・U17b の完了照合

| 要件 | 検証済みの公開 API・根拠 |
|---|---|
| 原典の片側仮定を固定 | 原典照合記録と `localKFlat`。全 Hom(−,b)、または全 Hom(b,−) の一方が K-flat。対象対ごとの選言ではない |
| 明示的 dg 商と指定 Verdier 商の実際の比較 | `quotientVerdierLocalEquivalence`。関手部分は既存の `quotientVerdierComparison`、充満忠実性も構成済み |
| dg 圏の解像度・DG-DR 引用を使わない | 最終エントリの transitive project import を走査。普通の加群の射影置換・path 長 filtration と三角形の Hom 完全性から証明 |
| H⁰(Perf_dg(D/S)) と指定完備 Verdier 商 | `localPerfectQuotientEquivalence` と `localSmallPerfectQuotientEquivalence`。大小の dg モデルで三角同値 |
| U17c への接続形 | `localPerfectKaroubiFirstEquivalence` と `localPerfectPaperSequenceComparison`。既存の順序交換同値・比較自然同型への実際の後置 |
| M9 の平坦 Hom からの供給 | `localQuotientTriaEquivalence_of_flat_zero` と `localPerfectQuotientEquivalence_of_flat_zero`。元の Hom が次数零に集中し、その次数零加群が平坦なら適用できる |
| 記録・正本への参照 | この文書に各単位を記録。`dg-theory.md` §15.5・§15.7 の既存の一行参照を維持し、本文には追記しない |

この担当目標の点ごとの比較と三角同値は完了した。残す U16 の自然性は、依頼で明示的に
後回しを認められた部分である。具体的には、S を対応させる Morita 比較に対して、
誘導される Verdier 商・Karoubi 完備化の関手と上記の perfect enhancement 比較の可換 square、
およびその自然変換・合成との整合性を追加する作業。これを今回の証明の仮定として隠していない。
U17c 全体の線形・shift 付き square や U17d の係数変更・作用との自然性まで完了したとは主張しない。

M9 の適用については、商を取る前の次数零の平坦 Hom を持つ dg 圏から必要な K-flat 性が得られる。
商の Hom が非正次数にあるというだけの主張では足りない。一般の係数環 T 側には T 上で同じ
平坦 Hom の入力を供給する必要があり、T の A 上平坦性を無条件に仮定することでは代用しない。


## 追加担当：U17c・U17d の独立部分と U17b の Morita 自然性（進行中）

- U17c は既存の順序交換同値・論文の列比較との正方形に、線形性・shift・三角性を付ける。
- U17d の今回の対象は係数変更、支持、retract の個別の図式。
  **中心作用・群 G の作用の比較は保留**。U16d の中心作用と M9 の適用範囲が固定されるまで着手しない。
- U17b の Morita 自然性は U16a の公開 API と U16b の受入を待つ。
  着手時点で `formalization-plans/dg-theory-morita.md` は未作成であったため、先に独立部分を進める。
- 既存の Morita/・Resolution/・Derived/・Endomorphism/・Perfect/ 等は編集しない。
  実装・監査ファイルは新設の Verdier/ または Quotient/DerivedComparison* に置く。

### U17c1：既存の局所 dg 商・perfect 比較の係数環上の線形性

- `Verdier/ComparisonLinear.lean`：ホモトピー有限 cell–tria 比較、finite cell の Karoubi–Perf 比較、
  既存の `quotientVerdierComparison`、局所 perfect 比較と小さい perfect 比較の線形性を公開した。
- underlying の dg 延長・主導来局所化・Karoubi 関手延長の既存の線形性を合成し、
  充満部分圏への制限と局所化の線形関手の判定を用いる。
  局所版には既存の二つのモデルの自然同型で線形性を運ぶため、新しい Morita 入力は不要。
- `localPerfectKaroubiFirstEquivalence` の順関手も線形になり、逆関手は既存の同値の
  inverseLinear から従う。元の比較の既存ファイルは編集していない。
- 対象ビルド `Verdier.ChecksComparisonLinear` 成功（2788 jobs）、警告なし。
  主要6宣言の公理監査は標準3公理のみ。project import 依存を走査し、禁止された
  dg 圏分解系への依存なし。新規 sorry・axiom・引用なし。
- U17c 全体は未完。比較自然同型そのものの shift 整合性と、U17d の各図式を続ける。


### U17c2：順序交換・論文の列比較・局所 perfect 比較の構造付き正方形

- `Verdier/OrderSquare.lean`：既存の `karoubiVerdierOrderEquivalence` と元の圏からの標準関手が
  作る `orderSquare` を、関手合成の結合同型を明記して構成した。
  比較自然同型そのものが整数 shift と可換であることを証明。
  三角性を持つ各辺に加え、`orderSquareTriangle` で実際の三角形関手間の自然同型も公開する。
- dg 側の `triaKaroubiComparison` と、論文の `paperRankEquivalence`・`paperSequenceComparison` が
  この同じ正方形の特殊化であることを、自然同型の等式として証明した。
  元の比較の既存ファイルや関手の定義は変更していない。
- `localPerfectOrderSquare` は局所 K-flat perfect 比較への後置を、結合同型付きで明記したもの。
  既存の `localPerfectPaperSequenceComparison` と実際に等しいため、元の比較そのものにも
  `NatTrans.CommShift` を与えた。`localPerfectOrderSquareTriangle` が三角形レベルの正方形。
- `localPerfectKaroubiFirstEquivalence` に順逆の shift 整合性と三角同値の証明を追加。
  前段の線形性と合わせ、正方形の辺は線形三角関手である。
  `orderSquare_naturality_smul` はスカラー倍した射に対する線形な自然性の式を公開する。
  `paperSequenceComparisonTriangle` は論文の列比較そのものの三角形関手への正方形。
- 対象ビルド `Verdier.ChecksOrderSquare` 成功（3621 jobs）。新規ファイル自身の警告なし。
  主要13宣言の公理監査は標準3公理のみ。project import 依存661ファイルを走査し、
  dg 圏分解系への依存なし。新規 sorry・axiom・引用なし。既存・他担当のファイルは編集していない。
- U16 の記録は作業中に新設された。`dg-theory-morita.md` の「U16a 公開 API」節を読み、
  主導来作用・unit/counit・作用の合成比較はまだ型のみ確定であることを確認した。
  `dg-theory-morita-qe.md` では U16b の Perf・小さい enhancement の部分が検証されているが、
  kernel 主導来作用との関手自然同型は未実装の段階である。
  予定型を証明済み宣言として import せず、U17b の自然性は受入済みの範囲を見て接続する。
- 残部は U17d の係数変更・支持・retract の個別の図式と、U16 受入後の Morita 自然性。
  中心作用・G 作用は引き続き保留。U17c1 のコミットは `29c75ef9`（自分の3ファイルのみと確認）。

### U17d1：retract と形式的直和因子の個別の比較図式

- `Verdier/RetractSquare.lean`：完全忠実な関手の像の間の retract を、分裂単射と分裂全射の
  両方ごと引き戻す `comparisonRetractPreimage` を構成。両射の map が元の射に等しいことを
  `comparisonRetract_i_square`・`comparisonRetract_r_square` として公開した。
- `localTriaRetract_iff`・`localPerfectRetract_iff` は、実際の局所商・perfect enhancement 比較が
  retract 関係を保存・反映することを述べる。完備化上では `localCompletedRetract` により
  Karoubi の標準 retract を運び、その二つの分裂射の underlying map が元の冪等元の像と
  一致することと、分裂の等式をそれぞれ証明した。
- 対象ビルド `Verdier.ChecksRetractSquare` 成功（2789 jobs）、新規ファイルの警告なし。
  主要9宣言の公理監査は標準3公理の範囲内。新規 sorry・axiom・引用なし。
  既存の比較や他担当ファイルは編集していない。U17c2 は `8b27ed9d`（自分の3ファイルのみ）。
- この単位は U16 に依存しない。支持・係数変更・U16 受入後の自然性は引き続き進行中。

### U17d2：支持部分圏への制限と忘却正方形

- `Verdier/SupportSquare.lean`：線形同値の支持部分圏への制限と、元の同値への忘却の
  `supportForgetSquare` を構成。線形性、比較自然同型の shift 整合性、三角形関手への
  `supportForgetSquareTriangle` を公開した。
- 実際の局所 tria 商比較、Karoubi 完備化された比較、perfect enhancement 比較をそれぞれ
  `localSupportedTriaEquivalence`・`localSupportedCompletedEquivalence`・
  `localSupportedPerfectEquivalence` として制限し、三角同値と忘却正方形を与えた。
  支持の条件は同じ有限個のスカラーの共通の正の冪による恒等射の消去であり、
  `localTriaSupport_iff` で保存だけでなく反映も明記している。
- 支持部分圏の shift を構成するため、加群評価・加群 shift・導来 shift・tria shift の線形性を
  既存関手から証明した。perfect enhancement の実際の shift の線形性は、完全忠実な
  perfect 比較とその shift 同型から反映する。既存ファイルの shift の定義は変えていない。
- 対象ビルド `Verdier.ChecksSupportSquare` 成功（2793 jobs）、新規ファイルの警告なし。
  主要14宣言の公理監査は標準3公理のみ。新規 sorry・axiom・引用なし。
  直前の retract 単位 `ac38cc8e` はコミット直後の `git show --stat HEAD` で自分の3ファイルのみと確認。
- 残る独立部分は係数変更。U16a の記録は依然として主導来作用・一般随伴・合成作用比較が
  「型のみ確定」であり、U17b の対応する自然性は未受入の宣言を前提にしない。
  中心作用・群 G の作用は保留を維持する。

### U17d3：非平坦係数変更の tria・Perf・完備商上の図式

- `Verdier/ScalarExtensionSquare.lean`：U12f の実際の主導来係数拡大を Perf に制限し、
  U15d の `quotientBaseChangeDGFunctor` に沿う実際の導来延長を後置した
  `quotientScalarPerfectFunctor` を構成した。包含正方形はこの二つの元の導来関手の
  合成へ戻る。A′ の A 上平坦性も Hom の全体的な平坦性も仮定しない。
- 既存の U14 の構造付き Perf 係数変更を読み、整数 shift・三角性を引き継いだ。
  既存の perfect enhancement の H⁰ へ運んだ関手と主 Perf の比較正方形、その
  shift 整合性と三角形関手への自然同型も公開した。新しい dg 関手を H⁰ の運搬だけから
  構成したという主張ではない。入力 dg 関手は U15d の固定 path 比較そのものである。
- `completedScalarExtension` は既存の局所 perfect 同値に沿って完備 Verdier 商へ運んだ関手。
  両係数環での `localKFlat` は独立の明示入力。`localPerfectScalarExtensionSquare` と
  その shift・三角形版が局所 perfect 比較との正方形である。
- `Verdier/ScalarExtensionTria.lean`：完全な Perf 関手が代表加群を tria に送れば
  tria 全体を tria に送ることを生成性から証明。係数変更と固定 path 比較の合成での
  代表加群の像を `quotientScalarRepresentableIso` で具体的に計算し、
  実際の導来関手の tria 制限 `quotientScalarTriaFunctor` を得た。
  tria→Perf および主導来包含との正方形は元の射写像のまま可換する。
- `localScalarTriaExtension` は未完備の指定 Verdier 商に局所同値を使って運んだ関手。
  `localScalarTriaSquare` は局所比較との shift 整合な正方形、
  `canonicalScalarTriaSquare` は既存の指定 `quotientVerdierComparison` そのものとの正方形。
  **構成の範囲**：元の D 上で先に係数変更を行い、その後 Verdier 局所化して得る別構成と
  この運搬の一致までは証明していない。canonical square の自然同型そのものの shift 整合性も
  既存の二モデル比較の構造との照合として残る。局所 square の shift・三角形版は証明済み。
- 対象ビルド `Verdier.ChecksScalarExtensionSquare` 成功（3365 jobs）、新規ファイルの警告なし。
  主要18宣言の公理監査は標準3公理のみ。新規 sorry・axiom・引用なし。
  既存の Derived/・Endomorphism/・Morita/・Quotient/ のファイルは読み取りのみ。
- 前単位 `88d231ca` は直後の stat で自分の3ファイルのみと確認した。
  ルート・README・Stage・正本の共有本文は今回編集・stage していない。
- 最新の `dg-theory-morita.md` の **U16a2** では通常 bimodule 上の
  `kernelDerivedTensorOnBimodule` と任意射影解像度計算、graph と `dgDerivedExtension` の
  関手の等式が実装・検証済みとなった。冒頭の古い状態表だけを見て「通常作用しかない」とはしない。
  ただし主導来 kernel 全体の `kernelDerivedTensorFunctor`、一般随伴、恒等・合成作用比較は
  未実装であり、U17b 全体の自然性は未完。中心作用・G 作用の保留も維持する。

### U17b1：実際の graph 作用と誘導 Verdier 関手・完備化・perfect 比較

- U16a2 の実装済み部分を読み、一般 kernel 全体を待つ必要のない graph の自然性を進めた。
  `Quotient/DerivedComparisonFunctoriality.lean` は F : D→E と F(S)⊆T から、標的商の
  標準 ε を指定収縮に取る実際の `quotientDGFunctor` を厳密普遍性で構成する。
  包含との厳密な正方形、ε の像、対象の像を公開した。
- `Verdier/DerivedGraphComposition.lean` は objectwise 制限の合成自然同型を主局所化へ降ろし、
  既存の実際の延長–制限随伴の一意性から導来 graph 延長の合成自然同型を得る。
  置換後の tensor 合成を無条件に同一視したり、左側 kernel の K-flat 性を省略したりしない。
- `Quotient/DerivedComparisonGraphSquare.lean` は実際の graph 導来延長を tria に制限し、
  F(S)⊆T が tria(S)→tria(T) を与えることを証明した。その後 **元の tria 関手を先に
  Verdier 局所化** して `graphVerdierFunctor` を構成する。
  `graphDerivedQuotientSquare`・`graphLocalVerdierSquare`・`graphCanonicalVerdierSquare` は
  その関手と明示的 dg 商側の実際の graph 作用との自然同型である。
  この比較自体には局所 K-flat 性も F の擬同値性も不要。
- `Verdier/KaroubiFunctorSquare.lean` は実際の正方形の Karoubi 延長と、tria→Perf 正方形から
  既存の finite cell Karoubi–Perf 比較への自然性を構成する。係数環の違う場合も扱い、
  前単位の係数変更についても `quotientScalarKaroubiPerfectSquare` を得た。
- `Verdier/GraphPerfectSquare.lean` の `graphCompletedVerdierSquare` は、上で本当に局所化した
  関手を Karoubi 延長し、既存の `localCompletedQuotientEquivalence` と可換にする。
  両側の局所 K-flat 条件は独立に明示する。`graphLocalPerfectSquare` は既存の
  `localPerfectQuotientEquivalence` そのものと、商 dg 関手の実際の導来延長の Perf 制限を
  使った enhancement の H⁰ 関手との正方形である。運搬で Verdier 関手を定義したのではない。
- 各 graph tria/Verdier/完備関手は整数 shift と三角性を持つ。H⁰–Perf の比較自然同型も
  shift と整合し、三角形関手への正方形を公開した。ただし主要な導来合成・局所比較の
  **自然同型そのものの shift 整合性** は未照合。全ての square を構造付きとする主張はしない。
- `Verdier/GraphKernelSquare.lean` は U16a2 の実際の `kernelDerivedTensorOnBimodule` を
  graph に適用した正方形を公開する。対象ごとの計算だけでなく、全導来対象・全射に自然な
  関手自然同型である。主導来 kernel 全体の未実装の関手を入力仮定として隠していない。
- 対象ビルド `Verdier.ChecksGraphPerfectSquare` 成功（3579 jobs）、新規警告なし。
  主要22宣言の公理監査は標準3公理のみ。新規 sorry・axiom・引用なし。
  既存・他担当ファイル、共有ルート・README・Stage は変更していない。
- 前単位 `ef74a640` は直後の stat で自分の4ファイルのみと確認済み。
  残部は係数変更の元の tria からの局所化構成との一致、比較自然同型の構造照合、
  主導来 kernel 全体と恒等・合成・自然変換の受入後の自然性。中心作用・G 作用は保留。

### U17d4：tria の Karoubi 延長と perfect 比較による係数変更の経路一致

- `Verdier/ScalarCompletionSquare.lean`：未完備の指定商上で既に構成した係数変更の
  Karoubi 延長 `scalarCompletedTriaFunctor` を取り、前単位の tria–Perf 正方形の
  Karoubi 延長と既存の完備化比較を貼り合わせた。
- `scalarCompletedTriaSquare`・`scalarCompletedPerfectSquare`・
  `scalarCompletedLocalPerfectSquare` は、tria の完備化、主 Perf、実際の局所 perfect
  enhancement 比較を結ぶ個別の正方形である。
- `scalarCompletionComparisonIso` は、この Karoubi 延長と、先に perfect 比較から
  完備商へ運んだ **既存の** `completedScalarExtension` との関手自然同型。
  比較同値による前合成の充満忠実性から構成し、全射について自然である。
  `scalarCompletionToKaroubiSquare` は未完備商からの標準包含を含む実際の完備化正方形。
- 係数環の平坦性は仮定せず、変更前後の `localKFlat` を別々に受け取る。
  両辺の shift・三角性は既存構造を保つ。ただし経路比較自然同型そのものの shift 整合性は
  新たな構造照合の課題として残す。この単位で係数変更の元の D からの別の局所化構成まで
  同一視したという主張ではない。
- 対象ビルド `Verdier.ChecksScalarCompletionSquare` 成功（3403 jobs）、警告なし。
  主要6宣言の公理監査は標準3公理のみ。新規 sorry・axiom・引用なし。
  前単位 `d93b6385` は直後の stat で自分の8ファイルのみと確認した。
- 目標全体は進行中。U17c と支持・retract は検証済みだが、上記の係数変更の直接構成との
  比較・構造照合、一般 Morita kernel の受入後の自然性を残す。中心作用・G 作用は保留。

### U17b2：主導来 kernel の局所化上の graph 作用への接続

- U16a3 の最新記録と `Morita/KernelDerivedFunctor.lean` を読み、
  `kernelDerivedTensorFunctor`・`kernelDerivedTensor` が主導来 kernel の射も含めて
  実装・検証済みとなったことを確認した。以前の「未実装」という記録は当時の状態である。
- `Verdier/DerivedKernelGraphSquare.lean` は、この実際の主導来作用の `kernelGraph` における
  値を `kernelDerivedTensorOnBimoduleIso` と graph 一致で既存の導来 graph 延長へ比較する。
  `derivedKernelGraphQuotientSquare` は、包含と誘導商関手の4辺を **主導来 kernel 上の作用** に
  置き換えた、全導来対象・射に自然な正方形である。
- `derivedKernelGraphPerfectFunctor` は主導来 kernel 作用そのものの Perf 制限。
  元の graph 延長の Perf 制限への自然同型を構成した。
  `derivedKernelLocalPerfectSquare` は、前単位で元の tria から本当に局所化した完備 Verdier
  関手と、この主導来作用を用いた H⁰ 関手が既存の局所 perfect enhancement 比較と可換に
  なることを示す。商を取る両側の局所 K-flat 条件を独立に明示する。
- 対象ビルド `Verdier.ChecksDerivedKernelGraphSquare` 成功（3582 jobs）、警告なし。
  主要7宣言の公理監査は標準3公理のみ。新規 sorry・axiom・引用なし。
  U16a・U16b 側のファイルは読み取りのみ。
- これは graph kernel の場合の実際の主導来接続であり、任意 kernel の商への降下や
  恒等・合成・自然変換の全 coherence まで完了したという主張ではない。
  構造照合と係数変更の直接構成との一致を継続する。中心作用・G 作用は保留。
