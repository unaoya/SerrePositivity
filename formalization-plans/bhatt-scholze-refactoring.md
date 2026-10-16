# Bhatt–Scholze 形式化のリファクタリング計画

作成日：2026-10-16。BSの証明済み構成を保ち、既存APIの再利用、一般補題の配置修正、重複証明の統合を順に行う。
原典証明の正本は[BS計画](bhatt-scholze.md)、担当・待合せ・合流の正本は[CLMST計画 §0.2](clmst.md)とする。
この計画は証明経路や引用範囲を変更しない。B3の存在・普遍性、B4の一般全射性を維持し、B5の新しい数学とは分ける。

§8の再調査は、ユーザーの「コードを書き換えない」という指定に従い、計画書のみを更新した記録である。
その後の目標継続指示により、この計画に沿うBS独立部分の実装・検証・個別コミットを再開する。
共通担当のファイルは変更せず、既存の未コミット差分を先に検証・保存する。
現在の実施順・担当・受入条件は§12を優先する。R1〜R6の完了記録は§9、N1〜N3は§11、§10はその実装途中の調査と並行移管の記録である。
過去の件数と検証記録は各実施時点の記録として読む。

## 1 調査の基準

調査時点のBS層は569モジュール、54,610行。宣言とimportを全件棚卸しし、Lean環境の10,710宣言と、ソースから抽出した3,144件の公開定義・定理等を照合した。
証明本文は重複候補、仮定削減候補、依存循環の懸念箇所と利用先を重点確認した。
再点検時の作業ツリーは571 Leanモジュール、54,507行（新規2ファイルを含む）。全importグラフに循環はなく、
既存監査の528 import対象のビルド、基礎監査584件、B4監査2,560件が成功した。
この件数は既存差分込みのBS検証であり、並行作業を含むプロジェクト全体の検証とは分ける。
各候補の分類は次のとおり。

- **再利用**：既に証明済みのAPIへ置き換える。公開名・型・標準射の公式を保つ。
- **抽出**：複数の利用箇所の共通部分を一般補題として取り出す。必要な仮定と具体的な射を明示する。
- **証明拡張**：仮定削減や相対化を伴う。機械的な移動・短縮とは別コミットで検証する。
- **保留**：利用需要、比較証明、共通側の公開APIが揃うまで既存構成を保つ。

## 2 担当と不変条件

BS側が変更するのは `SerrePositivity/BhattScholze/`、このBS計画、BS専用監査。
共通の `CommutativeAlgebra/`・`HomologicalAlgebra/`、`CLMST/`、`RootTower/`、DG・ホモトピー基盤、ルート `SerrePositivity.lean`、共有監査は変更しない。
新規一般δモジュールも当面BS内に置く。共通層への移管はファイルと担当の合意後に行う。
既存の別チャットへの送信はこの計画だけでは許可されない。

維持する条件：

1. `IsIntegralPerfectoid`、`IsPerfectoidization`、`DerivedTensor`、完全平坦性等を再定義しない。
2. W₂切断によるδ構造を維持し、pねじれ、零環、異なる宇宙の一般性を失わない。
3. B3の完備性を要求しない一般全射商の存在入口と、B4の導来p完備商の全射性を分ける。古典的完備性への移行には既存比較を使う。
4. 同型の存在だけでなく、基底射・単位・係数・変数・生成元上の式を維持する。
5. 同じ台集合上の異なる代数作用を混同しない。局所instanceを無条件のglobal instanceへ変更しない。
6. 新しいsorry、公理、外部引用を追加しない。B-Iの整代数の存在引用は削除・弱化しない。
7. 既存の選択対象を不要に再選択しない。旧新の写像を変更する場合は一致を証明する。
8. 共有作業ツリーの他作業を上書き・一括ステージしない。自分の対象ファイルを明示してコミットする。

## 3 BS側の実施順

各行は独立した検証・コミット単位に分割できる。共通担当待ちの工程だけを保留する。
実施順は既存API再利用、δ・DPの配置と構成の抽出、普遍性・具体的表示の比較、仮定削減・相対化の順。
既存差分の検証・保存を先に行い、後続の試作はその区切りまで作業ツリーに反映しない。
「試作済み」「ビルド・監査済み」「コミット済み」を区別し、完了は検証とコミット後に記録する。

| ID | 内容 | 分類 | 主な対象 | 状態 |
| --- | --- | --- | --- | --- |
| R0 | 調査結果・契約・検証条件を保存 | 文書 | この計画 | 記録済み |
| R1a | 有向極限の平坦性を既存APIへ置換 | 再利用 | `DeltaDivisionNormalizedDirectLimitFlat` | 完了 |
| R1b | Tor余極限の零性、初期剰余の自由性・忠実平坦性を既存APIへ接続 | 再利用 | `DeltaDivisionSourceEvaluationColimitTor`、`DeltaRootFamilySourceColimitTor`、`DeltaDivisionBoundedSupportTor`、`DeltaDivisionFirstResidueFlat` | 完了 |
| R1c | support・一次多項式正則性をMathlibへ接続 | 再利用 | `RelativeFreeWittInverseSupport`、`DeltaDivisionFiniteRelationsRegular` | 完了 |
| R1d | 零完備性・係数制限・商射の外延性を既存APIへ接続 | 再利用 | `PerfectDeltaPDQuotientEquiv`、`PerfectDeltaPDQuotientComparison`、`PDCompletionInterface`、`OrientedPrismHom` | 完了 |
| R2a | W₂写像と逆δ射を低層へ移す | 配置 | 新 `WittTwoMap`、`DeltaRing`、`DeltaQuotient`、`DeltaSectionNaturality`、直接利用先 | 完了 |
| R2b | 環同型によるδ構造移送を統一 | 抽出 | 新 `DeltaTransport`、`DeltaDivisionSourceTensorDelta`、`DeltaRootSourceRawH0Delta` | 完了 |
| R2c | 変数のδ値を指定する多項式構成とδ射判定 | 抽出 | 新 `PolynomialDelta`、`RelativeFreeDelta`、`PolynomialRankOneDelta`、普遍性利用先 | 完了 |
| R2d | 有向環余極限上のδ構造と普遍射 | 抽出 | 新 `DeltaDirectLimit`、`DeltaPerfection`、`DeltaPerfectionUniversal`、`DeltaAdjoinDivisionFiniteColimit` | 完了。534対象ビルド・基礎/B4・新7宣言監査、旧完全署名の一致を確認 |
| R2e | δ閉包の生成元定理を基礎層へ集約 | 配置・再利用 | `DeltaClosureGeneration`、`DeltaDivisionIteratedRelations` | 完了 |
| R3a | rank-one DPの一般比較射を分離し特殊版を一般版へ委譲 | 配置・再利用 | 新 `RankOneDPBaseChangeMap`、`RankOneDPTensorRelations`、`RankOneDPAnyBasis`、`RankOneDPPrimeBasis`、`RankOneDPBaseChange` | 完了 |
| R3b | principal DPの一般関係式を分離し基底変更を一本化 | 配置・再利用 | 新 `PrincipalDPBaseChangeRelations`、`PrincipalDPBaseChange`、`PrincipalDPBaseChangeUniversal` | 完了 |
| R3c | DP表示の正則性で不要なp局所性を外した一般入口 | 証明拡張 | `PrincipalDPRegular` | 完了。一般入口2件と旧包装2件の監査、旧完全署名の一致を確認 |
| R4a | 初期係数表示を既存モニック表示比較へ接続 | 再利用・比較 | `DeltaDivisionFirstCoefficientPowerEquiv`、`MonicPowerFamilyBaseQuotient` | 完了 |
| R4b | 根関係式の通常の冪指数を非零指数に一般化 | 証明拡張 | 新 `MonicPowerFamilyRelationRegularity`、`DeltaRootRelationKoszul`、`DeltaRootSubsetQuotient`、`DeltaRootFiniteRegularSequence`、`DeltaDivisionSourceGraphKoszul` | 完了。新6宣言・源グラフ利用先の監査、旧24完全署名の一致を確認 |
| R4c | hpAからhpL・ghost単射を供給する公開入口を揃える | 再利用 | `DeltaRootSourceRegularGhost`、`DeltaRootFamilyRegularGhost`、`DeltaRootFamilySourceQuotientFlat`、`DeltaRootBoundedSupportQuotientFlat` | 完了。旧22完全署名と6入口の監査を確認 |
| R5a | 未完備perfection・合成標準射のhom_extと既存PD外延性の適用 | 抽出 | `DeltaPerfectionUniversal`、`DeltaPerfectionPDCompletionUniversal`、`DeltaPerfectionPDCompletionComparison` | 完了。新3宣言・選択済み順逆射のrflを確認 |
| R5b | 完全prismのWitt表示とイデアル像の入力供給 | 抽出 | 新 `PerfectPrismWittPresentation`、`PerfectPrismHomLift`、`PerfectPrismQuotientPerfectoid` | 完了。新12宣言・旧表示のrfl契約を確認 |
| R5c | 単一根の上位perfectoid証明を任意族から特殊化 | 比較 | 新 `CompatibleRootSingletonComparison`、`CompatibleRootCompletionPerfectoid` | 完了。新10比較・標準射・一般終域契約を確認 |
| R6 | 相対δのイデアル冪評価・剰余算術を共有 | 証明拡張 | 新 `RelativeDeltaEstimate`、`DeltaAdicEstimate`、`RelativeFreeFiniteDeltaAdicEstimate`、`DeltaResidueArithmetic`、`RelativeFreeFiniteDeltaResidue` | 完了。新9宣言・移動1宣言・旧18利用先を監査 |
| R7 | BS監査の宣言列挙・公開境界検査、文書の現況整理 | 監査・文書 | BS専用スクリプト、BS計画 | 構造監査は実装済み。並行移管後の互換性確認と§11の分類整理を続ける |

### R1の既存API

`moduleDirectLimit_flat` は非空有向図式の平坦加群の `Module.DirectLimit` を扱い、遷移射の単射性を要求しない。
BS固有の環余極限との線形同型と、それによる平坦性の移送は残す。
Torの零性には `TorSequentialColimits`・`TorExactColimits` を使う。条件付き入口のcolimit保存仮定がある場合は、その型を維持する。
`MonicPowerFamilyPolynomialFlat`、`MvPolynomial.eval₂_mem`、`Polynomial.mem_nonZeroDivisors_of_leadingCoeff`、`isModuleComplete_zero`、`isModuleComplete_algebraMap_iff`、商射のMathlib APIを優先する。

### R2の契約

- W₂写像：任意の環射 `f : A →+* B` に対する `WittTwo p A →+* WittTwo p B` と座標式。商の構成をimportしない。
- 同型移送：`E : DeltaStructure p B` と `e : A ≃+* B` からδ構造を構成し、`δ_A x = e.symm (δ_B (e x))` と両方向のδ射性を供給する。
- 多項式構成：`D : DeltaStructure p A` と `v : σ → MvPolynomial σ A` から `δ(C a)=C(δ a)`、`δ(X s)=v s` を得る。rank-one版はv=0、相対自由版は次段変数。
- 余極限：各段の明示的δ構造とδ遷移射から既存 `Ring.DirectLimit` にδ構造を与え、標準段射・適合する普遍射のδ射性を証明する。
- 閉包：任意集合sについて `δClosure(span s)` をδ反復像のspanで表示する。イデアル全体の版は特殊化する。

`IsDeltaHom.symm` は完全性を使わないため一般δ射層へ移す。商APIを推移的importだけで使っていた `FreeDeltaPresentation`・`RelativeFreePresentation` 等には、必要な直接importを明示する。
多項式δ射判定は任意の既存多項式δ構造にも適用できる形とし、自由整数δ環は再定義しない。
δ余極限では同じ台型・遷移射と `section_of`・`delta_of`・`lift_of` を保持する。
R2dでは抽出を実装・検証済み。今後さらに仮定を削減する場合は、現在の公開署名と構成を基準に別工程とする。

### R3の依存方向

調査開始時は `AnyBasis → BaseChangeUniversal → TensorRelations → BaseChange → PrimeBasis` というimport依存のため、特殊基底を一般基底に単純置換すると循環した。
一般比較射の分離後は `BaseChangeMap → TensorRelations → BaseChangeUniversal → AnyBasis → PrimeBasis` の順にする。
`AnyBasis` の整数・有理数による基礎証明は保持し、旧特殊版は一般版の互換入口とする。旧比較射の順射は同じまま保つ。
principal DPでも一般関係式が特殊版に同居しているため、先にその低層部分を分離する。
`PrincipalDPBaseChangeRelations` はBS担当でBS内へ新設する。順射と選択済み逆射を保つため、
特殊版の同型構成本体は維持し、関係式・全単射性・生成元公式の証明を一般版へ委譲する。
正則性のp局所性削減は別工程であり、階乗部分環との比較が使うp局所性まで削除しない。

### R4からR6の比較条件

初期係数表示では、係数イデアルとモニック関係式の和との一致を証明してから既存同型を使う。旧新の射はC・X上で一致させる。
通常の冪根関係式で素数性を非零性にしか使わない部分は一般化できるが、δ恒等式の素数性は維持する。
hpL・hgは公開入口で内部供給し、選択された同型・代数作用を支える低層引数を一括削除しない。
普遍性の比較は既存の順射・逆射を固定し、hom_extで合成=idを示す。新しいchoiceを作らない。
`PDCompletionInterface.pdCompletionRingHom_ext` と `pCompletedDeltaHom_ext` は既存なので新設しない。
未完備perfectionの外延性を終域Frobeniusの単射性だけに弱める案は、既存普遍性の包装とは別の証明拡張とする。
Witt表示は零環を含む環同型・イデアル像・商比較と、標準Wittδとの両立に必要な `CharP` の層を分ける。
単一根の特殊化は一元添字族とのイデアル・商・完備化・標準射の比較を先に証明し、上位perfectoid性から行う。
第一係数商の試作で `quotEquivOfEq` の標準元比較にkernel timeoutが生じた。ソース短縮だけで採用せず検証時間も確認する。
相対δの評価では、環射fと相対W₂持上げを明示し、通常δ構造を全面的に相対構造へ再定義しない。
相対評価の仮定は `x ∈ (J.comap f)^(n+1)` とする。`f x ∈ J^(n+1)` への置換は一般には偽。
通常版はf=id、有限段版は元の段包含へ特殊化し、零環・pねじれ・変数包含の自然性を保持する。

## 4 共通基盤への移管候補

以下の共通ファイルはBS側では編集しない。実装依頼が必要になった時点で、BS主計画の要求欄にも登録し、送信はユーザーの許可に従う。

| ID | 対象と仮定・結論 | 既存APIで足りない点とBS利用先 | 待つ工程と独立作業 |
| --- | --- | --- | --- |
| Q1 | 任意IとR加群Mについて、標準商射の `scalarExtensionTorVanishing` と標準 `extendScalars` 剰余の `Module.FaithfullyFlat (R ⧸ I)` から `IsCompletelyFaithfullyFlat I M`。正則性・有限生成性・完備性は不要 | `CompletelyFlatCriterion` の一般判定と忠実版の包装。prism・PD・perfectoid拡大の五箇所 | この包装の統合のみ待つ。R1〜R6は独立 |
| Q2 | PreorderとOrderBot、単調部分加群Kᵢ、全射線形β、ker β=⨆Kᵢから商図式・標準cocone・IsColimit・段射公式 | 三つの評価余極限でmapQとdescを重複構成。現用版には有向性不要。最小元なしの一般化は別証明 | 三系統の余極限統合のみ待つ。有限段・核の計算はBS内で保持 |
| Q3 | 任意有限Sとs∉Sについてf(s)がR/span(f(S))上正則なら、任意nodupリストlに対し `IsWeaklyRegular R (l.map f)`。非自明性は追加しない | 三つのprefix-list証明。固定単元倍・環同型による移送は既存APIも確認 | 一般正則族の抽出のみ待つ。R4bはBS内の通常関係式として進める |
| Q4 | I.map f≤J、終域のJ完備性からAdicCompletion I Rの環射延長。存在にはI.FG不要。一意性にはI.FGとJ分離性 | MathlibのliftRingHomと共通線形外延性を使用。BS一般δ延長と共通p完備化で環射版が重複 | 共通への移管のみ待つ。δ射性の証明はBSに残す |
| Q5 | b導来完備M・線形Lなら1-bL全単射。a,b完備ならa+b完備。n≠0でa^n完備ならa完備 | `DeltaFrobeniusComplete` のδ非依存private補題。倍数閉性は既存 | 共通閉性APIへの移管のみ待つ。既存証明を維持 |
| Q6 | single Rの実導来反復完備化H0の反射性と標準単位 | 通常H0環の反復完備化の普遍性は既存。IteratedPDH0Reflectionのδ非依存証明を移管。任意加群への一般化は別工程 | 共通抽出のみ待つ。標準射の計算整理は独立 |
| Q7 | 環射φ、a,b、実導来対象Xについて Λ_b Λ_a Resφ X ≅ Resφ Λ_(φb) Λ_(φa) X と、合成された標準単位の等式 | `RestrictionCompletion` のG8を二回適用する二重実装。元の係数射と像の等式を保持 | 該当比較の統合のみ待つ。G8の追加要求ではない |
| Q8 | `IsCompleteModuleReflection R a B e`、各aⱼについて完備なR代数T、指定済み `E : B ≃ₗ[R] T` と `E e = 1` から、順射がEである代数同型 | ReflectionRing.linearMap_map_mulとAlgEquiv.ofLinearEquivで包装。両側の反射性は不要。実導来代数射を入力とするCompletedTensorH0Comparisonとは別契約 | 共通比較の抽出のみ待つ。BSのhom_extは独立 |
| Q9 | 正則d、`X : DerivedCategory.Minus (ModuleCat R)`、d導来完備性、正の各d冪への実導来還元の負次数消滅から `X.obj.IsGE 0` | 二箇所のMilnor再構成。G9のmod-d平坦性を勝手に仮定しない。IsLE 0と離散性は別入力・別結論 | 負次数消滅の共通化のみ待つ |
| Q10 | `[Fact p.Prime]`、hf:IsPerfectoidization p f、e:S'≃+*SからIsPerfectoidization p (f.comp e.toRingHom)。現行の同一universeを維持 | 終域一意性とは異なる源同型移送。RootedKernel/Presentationの二箇所。Cとfを再選択しない | 共通移送補題の導入のみ待つ |

RootTowerは任意段Aₙ上の平坦性のためcofinal tailの比較が必要で、BSの深さ図式と塔そのものを統合しない。
DG側の通常複体K-flat補題は共通化候補だが、相対DG作用は残す。ホモトピーstrictificationはBSの整理の開始条件にしない。
`ModulePower*` のうち通常商の遷移・標準Tor作用・実Tor塔・Milnor両端の比較は既に公開されている。
それらの具体的なAPIを再利用し、中央の係数環上の線形Milnor射と完備almost拡大閉性は別の待合せとする（§8）。
優先順はQ1・Q8・Q10、次にQ4・Q5・Q7・Q6、その後Q2・Q3・Q9。
CLMSTの標準Torの積・J²による零化は、元のイデアル自身の零化とB5のmod p冪像の冪等性とは別入力。
通常almost加群の拡大閉性は `Almost/Zero.of_exact_mul`・`of_exact` が既存であり再実装しない。
根生成イデアルとperfectoid化の核の比較を省略しない。RootTowerの明示基底・ランク・冪遷移は一般自由性だけで置換しない。

## 5 採用しない統合と後回しにする候補

- 一般Frobenius自然性が基礎のp正則版を使うため、基礎版を一般版で置換して循環させない。
- 自由整数δ環と相対自由δ環は既存比較を保持し、初期構成を一括で再定義しない。
- ghost値から係数が一意に決まるには正則性等が必要。ghost単射を無条件に消さない。
- 単一根と任意族は上位の完成定理から整理し、下位依存を全て逆転させない。
- 任意族の有限support・有界長方形・finalityの証明は数学的に必要であり削除しない。
- 平坦加群の有向極限の平坦性に遷移単射性は不要だが、忠実平坦性には追加制御が必要。
- `PerfectDeltaPDQuotientComparison` は候補のperfectoid性を先に仮定しない。IsPerfectoidization前提の反射定理へ置換すると循環し得る。
- prismの射はイデアル保存であり、選択生成元の厳密な一致を要求する定義へ変えない。
- B-I由来の選択とB3の商perfectoid化を同じchoiceに統合しない。
- 既存Koszul分解、perfectoid化の函手性、商テンソル比較を重複定義しない。
- 三角多項式自己同型の一般抽出、正則元の冪零摂動、δ閉包のClosureOperator化は追加利用需要を確認してから行う。
- 小ファイルの一括統合・フォルダ移動はAPIと依存が安定してから検討する。ファイル数そのものを削減目標にしない。

## 6 検証とコミット

各ステップで次を行う。

1. 対象ファイルの既存変更と担当を確認し、公開名・型・標準射の計算式を確認する。
2. 対象モジュールと必要な直接利用先を `lake build` する。低層変更ではBS監査の全import対象を再ビルドして推移的利用先も確認する。
3. BS専用の依存監査を実行する。既存の `scripts/audit_bhatt_scholze.lean`、`scripts/audit_bhatt_scholze_b4.lean`を用い、新規公開宣言もBS専用監査へ追加する。
4. 変更した定義・証明の公理を検査し、sorry・既存引用への依存を追加していないことを確認する。B-I引用系とAndré条件付き系は区別する。
5. `git diff --check` と対象差分を確認し、検証済みの自分のファイルだけを明示してステージ・コミットする。
6. この計画に実施項目、検証範囲、残る条件を記録する。共通担当待ちをBS独立工程の完了と混同しない。

監査の調査結果：BS専用監査のimport閉包は567/569モジュールで、残りはB-I引用系。商perfectoid化の公開七宣言はCLMST側監査にある。
`audit_clmst_b3.lean` の旧B-S sorry許可は共通担当による更新候補。BS側から共有監査を変更しない。
監査の自動列挙を導入しても、主要公開型・標準写像・引用境界の明示検査は残す。
再点検時の閉包は569/571モジュール（追加2モジュール込み）。共通フォルダ内でも
`PerfectoidIdeal`系列はB3接続層、旧perfectoid化との比較は引用互換層である。
基礎APIからBS・Inputsへの逆依存禁止と、接続・互換層の許可された依存を分けて検査する。
型検査では `#check @…` 相当の完全な暗黙引数・宇宙も確認する。未使用になった素数引数の脱落、
異なる局所Algebra/Moduleの混同、scratchとlakefileの設定差（maxSynthPendingDepth=3）を検証対象とする。

## 7 実施記録

- 2026-10-16 R0：調査結果、BS独立工程、共通移管候補、保留理由、検証条件をこの文書へ保存。既存の未追跡BS主計画や他担当の変更はコミット対象に含めない。
- 2026-10-16 R0再点検：読み取り調査で確認した既存API、相対δの正確な仮定、DPの選択保存、共通候補Q2/Q4/Q6/Q8の契約、並行作業と引用監査の境界を反映。既存差分込みの528対象ビルドと基礎584件・B4 2,560件の監査が成功し、標準3公理のみを確認。今後の抽出・一般化はこの検証に含めない。

- 2026-10-16 R1d：PD完備化の自己作用を標準射の `toAlgebra` と明示的な `Module` で固定し、既存の係数制限APIへ接続した。零完備性は既存の冪零化定理を使用し、商比較の代表元ごとの射の等式は `RingHom.cancel_right`、prism商射の全射性は `Ideal.quotientMap_surjective` へ置換した。対象4モジュールの `lake build` と新規BS専用 `scripts/audit_bhatt_scholze_refactoring.lean` が成功。公開7宣言に `assert_no_sorry`、変更した主要5宣言の公理は `propext`・`Classical.choice`・`Quot.sound` のみ。公開署名と具体的な比較射は維持。
- 2026-10-16 R2a：W₂係数写像の既存2宣言を低層のWittTwoMapへ、逆δ射の既存宣言をDeltaRingへ移し、直接利用先2箇所を適用に置換。商構成の必要な利用先には直接importを追加した。公開名・型と定義本体を維持し、新しい数学的宣言は追加していない。対象ビルド、528対象の統合ビルド、基礎584件・B4 2,560件の監査が成功。focused監査にも移動宣言と両利用先を追加し、sorry・追加公理・引用依存なし。

- 2026-10-16 R1a：正規化加群直極限の平坦性を既存moduleDirectLimit_flatへ委譲。元の段・遷移線形射・環直極限との比較は維持し、遷移単射性は追加していない。対象・直接利用先を含む528対象ビルド、基礎/B4監査、focused監査が成功。公開型を維持し、追加公理・引用依存なし。

- 2026-10-16 R1b：逐次・有限部分集合のTor消滅を共通G7 APIへ、初期剰余の自由性・忠実平坦性を既存monicPowerFamilyPolynomial APIへ委譲。元の評価図式・同型・係数作用と条件付き入口の引数は維持した。対象と下流を含む528対象ビルド、基礎/B4監査、focused監査が成功。追加公理・引用依存なし。

- 2026-10-16 R1c：多項式評価のsupport保存をMvPolynomial.eval₂_memへ、一次多項式の正則性を最高係数の非零因子判定へ委譲。零環枝と既存の一般性を維持した。対象と下流を含む528対象ビルド、基礎/B4監査、focused監査が成功。追加公理・引用依存なし。

- 2026-10-16 R3a：rank-one DPの比較射と2計算式をRankOneDPBaseChangeMapへ分離。一般基底を特殊基底の証明源にし、旧比較同型の構成本体と純テンソル式を維持した。一般比較のプロジェクトimport閉包は40から3、一般基底は41から5へ減少。旧素数instanceと引数順を明示して保持し、完全署名確認・focused型契約・528対象ビルド・基礎/B4監査が成功。追加公理・引用依存なし。

## 8 コードを変更しない再調査と実施案（2026-10-16）

### 8.1 現在状態を確定する

調査基準は `9088bf56` までの履歴と作業ツリー。BSは573モジュール・54,497行で、
未コミットの既存差分は変更7ファイル・新規2ファイルである。
これはソース棚卸しの値であり、今回の新しいビルド成功や証明監査の件数ではない。
既存ログと担当からの検証報告は保存するが、未コミット差分を完了扱いにはしない。

| 状態 | 項目 | 次の実装時にすること |
| --- | --- | --- |
| 検証・コミット済み | R1a〜d、R2a、R3a | 再実装しない。後続変更の回帰検査対象にする |
| 作業ツリー反映・対象ビルド済み | R2b（3ファイル）、R2e（2ファイル）、R3b（3ファイル）、R4a（1ファイル） | 既存差分を固定して統合ビルド・追加宣言監査を実行し、4単位で個別保存する |
| 一時ファイルのみで検査済み | R2c、R3c | repo未反映。新規適用として扱い、利用先と公理の監査を行う |
| 単体の試作のみ検査済み | R4b | 一般補題以外は未検証。一時検索パスの問題を解決した後に全利用先を検査する |
| 設計候補 | R2d、R4c、R5a〜c、R6、共通Q群 | 仮定・結論・具体的写像を固定してから着手する |

R2b/R2e/R3b/R4aの保存待ちを、追加の一般化と同じコミットに混ぜない。
R4aは旧26公開署名と9定義本体を維持する案であり、一般比較から全射性を得て旧逆射の右逆性を示す。
初期の `quotEquivOfEq` 案のtimeoutは、この最終案が未検証という意味ではない。
一方、対象ビルド成功を低層変更全体の統合監査成功へ読み替えない。

### 8.2 目標とする層と、抽象化の採否

目標は、同じ構成・証明の保守箇所を減らし、一般補題が特殊な表示や引用へ依存しない形にすること。
行数・ファイル数の削減そのものは完了条件にしない。現在の短い原典モジュールの粒度には、
依存と公理を限定して検査できる利点がある。

| 層 | 保持する対象 | まとめる内容 |
| --- | --- | --- |
| 共通基盤 | Witt、Tor、実導来完備化、反射、平坦性、perfectoidの既存定義 | δやprismを使わない一般補題。共通担当が所有する |
| BSの一般δ層 | W₂切断による `DeltaStructure` と `IsDeltaHom` | 同型移送、多項式構成、余極限、閉包、相対的な評価 |
| BSの具体的表示 | 自由δ環、δ除算包、DP表示、有限根族 | 選んだ環・商・順射・逆射を保持し、一般補題への適用を揃える |
| BSのprism・完備化比較 | 完全prism、Witt復元、元の実H0、標準単位 | 入力供給と外延性。選択済み比較を再選択しない |
| B3/B4公開境界 | 一般全射商の存在と、導来p完備商の全射性 | 利用側が構成の内部を展開せず使える入口を維持する |
| 接続・互換層 | perfectoid ideal、CLMSTの具体的商、旧引用名 | 証明済み入口への適用と、残す引用を別監査する |

一般化は「既存の複数の利用先に同じ型で適用できる」「具体的標準射を保つ」ことを採用条件とする。
結論として必要な完全平坦性・perfectoid性を新しい構造のfieldへ移すだけの包装は採らない。
δ環の圏全体、一般prismatic cohomology、新しい完備化対象を今回の抽出に持ち込まない。

### 8.3 BS側の具体的な次工程

1. **保存待ちの4単位を確定する。** 新しい抽出を混ぜず、同じソース状態で統合検証する。
2. **R2c：多項式δ構成。** 新 `PolynomialDelta` と既存
   `RelativeFreeDelta`、`PolynomialRankOneDelta`、`FreeDeltaUniversal`、
   `RelativeFreeUniversal`、`RelativeFreeSubsetSplit` を対象とする。
   `D : DeltaStructure p A`、`v : σ → MvPolynomial σ A` を入力とし、C/X上のδ公式とδ射判定を提供する。
   旧W₂ `eval₂Hom` と切断の定義的な一致を検査し、自由整数δ構造を作り直さない。
3. **R2d：δ余極限。** `DeltaPerfection` と `DeltaAdjoinDivisionFiniteColimit` の切断・段射・普遍射の証明を抽出する。
   同じ `Ring.DirectLimit` と関数反復による遷移を保持する。Frobenius段送りと完全性、
   有限族から全族への具体的比較は元のモジュールに残す。
   一般入口は `hom_ext` により非空性・有向性を要求せず構成できた（§9）。既存入口の仮定・署名は維持する。
4. **R5a/b：普遍射とWitt表示の重複。** `existsUnique_deltaPerfectionHom` を使う薄い外延性入口を追加し、
   完備化順序比較の既存順射・逆射の合成を同定する。既存のPD・p完備化外延性は再利用する。
   Witt表示では同じ `perfectDeltaWittRecoveryEquiv` とその生成元の逆像を固定し、
   イデアル像・商の公式・完備性を供給する。零環を含む環比較と `CharP` を要するδ両立は分離する。
5. **R3c/R4b/R4c：仮定と入口の整理。** DPのp局所性削減はp正則性・mod p正則性を残す。
   通常の根関係では `n ≠ 0` から `X s ^ n - C (c s)` の正則性を得る。
   零環・任意添字型を含め、Noether性・係数環の非零性・δ構造は追加しない。
   有限正則列と源グラフの指数1版へ適用し、δ恒等式の素数性は保持する。
   hpL/ghost単射はhpAから供給する上位入口を整え、同型や作用に関わる低層引数は残す。
6. **R5c/R6：比較証明を要する統合。** 単一根は一元添字族とのイデアル・商・完備化・標準射の比較を先に証明し、
   上位perfectoid定理だけを特殊化する。族版が使う単一根の低層は反転しない。
   相対δ評価は環射 `f : R →+* S` とW₂持上げを明示し、
   `p ∈ J` と `x ∈ (J.comap f)^(n+1)` から第1座標が `J^n` に入る一般補題へまとめる。
   通常版はf=id、有限段版は既存の段包含に適用し、有限段を自己δ環にはしない。

R2系列、R3系列、R5a/bの読み取り・契約確定は並行可能。
実装時には低層の型を先に固定し、共有する利用先を一人に割り当てる。
統合ビルド中は対象ソースを固定し、後続案はその検証へ混ぜない。
R5c/R6の比較が難航してもR2/R3/R5a/bの完成を妨げない。

### 8.4 並行作業との共通化

共通Q群は§4の契約で受け渡し、BS側から共通ファイルへ実装しない。
Q1〜Q10は既存証明の共通化候補であり、未受渡しの数学的入力G群とは異なる。
最小契約では新しい定理を外から仮定する必要はなく、待つのは共通入口への置換だけである。
優先度の高いQ1/Q8/Q10は既存一般理論の薄い包装であり、
Q4/Q5/Q6/Q7はBS内に残るδ非依存部分の移管、Q2/Q3/Q9は複数構成を横断する抽出である。
Q9のMilnor部分も既存 `MilnorAnnihilator` の適用を先に検討し、再構成そのものは作り直さない。

| 並行作業 | 現在再利用できる成果 | 今回まとめないもの・待つもの |
| --- | --- | --- |
| Torの実係数作用 | `TorAlgebraScalarComparison`、`TorAlgebraNaturality` | 新しいC加群構造を標準Torへ仮定しない。既存の実C加群への比較を使う |
| 冪商・Milnor | `ModuleTowerEquiv`、`ModulePowerTorAlgebraTower`、`ModulePowerTorAlgebraMilnor`、`ModulePowerTorAlgebraAlmost` | 元の遷移・係数作用・lim¹を保持。中央のC線形Milnor射と完備almost拡大閉性は未完了 |
| CLMSTの消滅 | `PowerTorsionTorProduct` の積・J²による零化 | Jによる零化、p冪ねじれ試験上のhTor、mod p冪像のhIは別入力 |
| almostの通常完全列 | `Almost/Zero.of_exact_mul` と `of_exact` | 後者は大域的な冪等性を使う。mod p冪像の冪等性だけの定理へ読み替えない |
| RootTower | `moduleDirectLimit_flat` 等の定性的補題 | 任意段を基底にする尾部の余極限比較が必要。明示モノミアル基底・ランク・冪遷移は保持 |
| DG・ホモトピー | 通常複体のK-flat性等を将来の共通抽出候補とする | 相対DG tensorの作用・結合比較、モデル構造、strictificationをBSの前提にしない |

通常商塔の再構成も `ModulePowerTensorHolim.modulePowerTensorReconstruction_quasiIso` が既存である。
各項の平坦性、テンソル複体の全次数に共通する冪ねじれ界、実導来完備性が入力であり、
同型対象の存在だけを新たに要求しない。実Tor塔のlim¹についても消滅は仮定していない。
Q6では通常H0環の反復と実導来対象の反復を定義上同じとせず、既存の標準単位を保つ比較を使う。

共通抽出の直接利用先を固定する：

| 候補 | 既存の一般API・抽出元 | BSで置換する箇所 |
| --- | --- | --- |
| Q1 | `CompletelyFlatCriterion.isCompletelyFlat_of_acyclic_flat_reduction` | `PerfectPrismRootPDCompletelyFlat`、`PerfectPrismDeltaAlgebraPDCompletelyFlat`、`PerfectPrismRootPrismCompletelyFlat`、`PerfectPrismRootPerfectoidCompletelyFlat`、`PerfectPrismRootedPerfectoidExtension` |
| Q8 | `ReflectionRing.linearMap_map_mul`、`AlgEquiv.ofLinearEquiv` | `DeltaRootRawCompletedH0Ring`。共通側の `PrincipalCompletionDerivedComparison`・`CompletedAlgebraPrincipalComparison` も同じ候補 |
| Q10 | `PerfectoidizationFunctor`・`PerfectoidizationUniqueness` | `RootedKernelSurjectivity`、`RootedPresentationSurjectivity` |
| Q4/Q5 | Mathlibのadic延長・`AdicCompletionExt`、`DeltaFrobeniusComplete`のδ非依存private補題 | `DeltaAdicLift`、`DeltaFrobeniusComplete`。共通側の `PerfectoidizationCompletion` と一本化 |
| Q6/Q7 | `IteratedPDH0Reflection`、`RestrictionCompletion` | `DeltaRootSourceIteratedCompletionComplete`、`DeltaRootRawCompletionRestriction`、`DeltaAlgebraPerfectionCompletionRestriction` |
| Q2/Q3 | 三系統の商余極限、有限prefixからの弱正則性 | `DeltaDivisionSourceEvaluationColimit`、`DeltaDivisionFamilySourceEvaluationColimit`、`DeltaDivisionEvaluationFiniteSupportColimit`、`DeltaDivisionFiniteJetFamilyRegularity`、`DeltaRootFiniteRegularSequence`、`DeltaDivisionSourceGraphKoszul` |
| Q9 | `MilnorAnnihilator`と既存の冪余核再構成 | `PerfectPrismRootSourceDiscrete`、`PerfectPrismDeltaAlgebraDiscrete` |

`CompatibleRootFamilyIdeal` の根生成イデアルの冪等性と、
`PerfectoidIdeal` の標準perfectoid化写像の核は、比較なしに同一視できない。
B5はこの具体的な核と完備導来テンソル・mod p冪比較を扱う別の数学的工程であり、
今回のリファクタリングやCLMSTのJ²零化だけでは完成しない。
B-IとAndréの既存引用も、共通化による削除対象にしない。

### 8.5 依存・公開境界・監査の改善

読み取りのimportグラフ検査では、プロジェクト内に循環はない。
`HomologicalAlgebra/` の452モジュールと `DifferentialGraded/` の665モジュールはBSへ到達しない。
`CommutativeAlgebra/` の396モジュールのうち9モジュールはBSへ到達する。
これらはperfectoid idealのB3接続、旧perfectoid化の引用互換、perfectoidねじれ商の系列であり、
フォルダ名だけによる一律の逆依存禁止は適切でない。
共通Q群の基礎入口にはBS・CLMST・Inputs・Paperへの逆依存を禁止し、接続層は明示した許可表で検査する。

BS基礎・B4監査の合成import閉包は568/573モジュール。
別のAndré条件付き監査とrefactoring監査も含めると571/573で、残る2件はB-I引用系である。
この**import被覆**は公開宣言の全件証明監査とは異なる。基礎監査の584件、B4監査の2,560件は
既存 `assert_no_sorry` の列挙数であり、新規・移動宣言と公開型の確認も別途必要である。

優先する監査改善：

- 共通担当の `audit_clmst_b3.lean` は161行以降で旧B-S入口をsorry許可に残し、表示も旧状況のまま。
  証明済みB4入口にはsorryを許さず、B-I・B-R・André条件付きの許可を別々に管理する更新候補とする。
- 同監査と `audit_clmst_rperfd_cohomology.lean` の証明依存探索は重複している。
  将来は型・値を辿る探索部分だけを共通化し、監査対象・許可・禁止・期待する引用は各監査に残す。
  BS単独では共有監査を変更しない。
- 公開型は宇宙・暗黙引数・素数instance・局所代数作用まで確認する。
  同型は順射・逆射・単位・C/X・純テンソル上の式を検査し、必要な `rfl` の成立も残す。
- ソース短縮に伴う型変換コスト増加を検査する。通常のheartbeat設定とlakefileの設定でビルドし、
  timeoutを上限増加だけで隠さない。既存の構成本体を保つ方法を優先する。
- BS主計画とCLMST計画の古い進捗文は履歴として残し、現在状態・公開入口・未解消入力を短い索引に集約する。
  CLMST側に残る「B4未完了」等の旧記載も担当側の更新候補とし、BS側から変更しない。

今回行ったのはソース・差分・既存検証記録の再調査と、この計画の更新である。
新しいLeanビルド・公理監査・コード適用・コミット・他チャットへの送信は実施していない。

## 9 計画に沿う実装の再開（2026-10-16）

目標継続指示に従い、既存のR2b/R2e/R3b/R4aを固定し、530件のBS監査import対象を再ビルドする。
以後の完了記録では、同じソースに対する統合ビルド・基礎/B4監査・追加公開宣言の監査を区別して記載する。
R2dとR5aは一時ファイルで独立に準備し、共通する `DeltaPerfectionUniversal` の反映は親担当が調整する。
R2dは同じ遷移関数によるMathlib余極限、R5aは既存完全性仮定と選択済み順射・逆射を保持する。
R4bも計画済み5ファイルの一時検証から再開する。これらを保存待ち4項目の検証ソースへ混ぜない。

- R2b：W₂切断の共役による `DeltaStructure.comapEquiv` とδ公式・両方向のδ射性を公開し、
  実テンソル源と実raw H0の二箇所へ適用した。異なるuniverse、零環、pねじれを許し、元の環同型・作用を保持。
  530対象・4,566ジョブの統合ビルド、基礎584件・B4 2,560件の監査、追加9宣言のfocused監査が成功。
  新4宣言と利用先の公理は標準3公理のみ。新sorry・引用依存なし。対象3モジュール・専用監査・計画を個別保存。
- R2e：指定生成元の全δ反復でδ閉包を表示する既存定理を一般δイデアル層へ移した。
  イデアル全体の反復像の定理をその特殊化に置換し、既存公開名・型を維持。新しい宣言は追加していない。
  同じ530対象・4,566ジョブの統合ビルド、基礎/B4監査、移動した定理と特殊化のfocused監査が成功。
  標準3公理のみ。対象2モジュール・専用監査・計画を個別保存。
- R3b：一般基底変更射の関係式を低層 `PrincipalDPBaseChangeRelations` へ移し、特殊版の関係式と生成元公式を一般版へ委譲した。
  旧 `principalDPBaseChangeEquiv` の構成本体・公開署名・選択済み逆射を保持。新しい公開宣言は追加していない。
  対象6入口のビルドに加え、同じ530対象の統合ビルド・基礎/B4監査・公開7宣言のfocused監査が成功。
  標準3公理のみ。対象3モジュール・専用監査・計画を個別保存。
- R4a：初期係数イデアルを基底イデアルとモニック関係式の和に同定し、既存一般比較の標準商元上の式と全射性を再利用した。
  旧26公開署名と9定義本体を維持し、旧順射・逆射・同型を再選択していない。
  対象ビルド、同じ530対象の統合ビルド・基礎/B4監査、新3宣言と旧比較入口のfocused監査が成功。
  標準3公理のみ。対象1モジュール・専用監査・計画を個別保存。

- R7構造監査：`scripts/audit_bhatt_scholze_structure.py` を追加した。
  コメント・文字列・属性・複数行のヘッダーと、循環・禁止経路・終了コードの9検査が成功。
  実ソースの構造検査も成功し、CompletelyFlat・DerivedTensor・WittGhostInjectiveの
  指定3入口にBS・CLMST・Inputs・Paperへの禁止依存はない。
  この時点のBS import被覆は574/576で、未被覆2件はB-I入力と互換入口。
  未被覆・宣言差分は参考警告、基盤入口未指定は未検査として表示する。
  Leanの証明・公理監査は既存スクリプトで別に行う。残る実装後に最終集計を更新する。

- R2c：変数のδ値を指定する多項式切断・δ構造と、係数/変数上でのδ射判定を共有した。
  切断のC/X計算補題も公開し、有限段自然性を下流のソース変更なしで復旧した。
  534対象・4,569ジョブ、基礎584件・B4 2,560件、追加10宣言と利用先のfocused監査が成功。
  R2c/R2d/R3cの旧75完全署名が変更前と一致し、旧二つのW₂ eval₂Homのrfl契約も成功。
  零環・pねじれ・異なる宇宙を維持し、新sorry・追加公理・引用依存なし。

- R2d：W₂切断をMathlibの同じ環余極限へ持ち上げる一般構成と、段射・普遍射のδ両立を抽出した。
  遷移は元の関数を保持し、新しい一般入口には非空性・有向性・単射性を要求しない。
  既存perfectionと有限部分集合余極限の公開署名・遷移・shiftは維持。
  534対象・4,569ジョブ、基礎584件・B4 2,560件、追加7宣言と旧3入口のfocused監査が成功。
  R2c/R2d/R3cの旧75完全署名が一致し、追加宣言の依存公理は標準3公理のみ。

- R3c：principal DP表示のmod p関係式の正則性とp正則性の一般入口から、不要なp局所性だけを除いた。
  素数性、係数環のp正則性、mod pの指定元の正則性は保持し、旧二つの入口は同じ型の包装として残す。
  534対象・4,569ジョブ、基礎584件・B4 2,560件、一般2宣言・旧2宣言のfocused監査が成功。
  旧完全署名は一致。新sorry・追加公理・引用依存なし。

- R4b：モニックな根関係式の正則性を任意の非零指数へ一般化し、有限正則列・Koszul性・指数1の源グラフへ適用した。
  係数環の非零性・Noether性・δ構造は要求しない。旧素数指数の入口と元の商・関係式・Koszul対象は保持。
  534対象・4,569ジョブ、基礎584件・B4 2,560件、追加6宣言と源グラフ利用先のfocused監査が成功。
  旧24完全署名が一致。新sorry・追加公理・引用依存なし。

- R4c：既存の平坦性によるp正則性移送とG4のghost単射を直接再利用した。新API・instance・同型は追加せず、低層で必要なhpP/hpL/hgと局所作用を保持した。旧22完全署名と6入口のfocused監査が成功。
  538対象の統合ビルド、基礎584件・B4 2,560件に加え、工程別の対象ビルドと集約focused監査が成功。
  新sorry・追加公理・引用依存なし。

- R5a：未完備perfectionと二つの合成完備化単位の外延性を公開し、既存の普遍性・比較同型の逆射検証へ適用した。完全性・二方向の完備性仮定と選択済み順射・逆射を保持。新3宣言を含む12入口のfocused監査と順逆射のrfl契約2件が成功。
  538対象の統合ビルド、基礎584件・B4 2,560件に加え、工程別の対象ビルドと集約focused監査が成功。
  R5/R6の旧37完全署名は変更前と一致。新sorry・追加公理・引用依存なし。

- R5b：同じWitt復元同型と生成元逆像を使う表示を抽出し、商のperfectoid性とprism射持上げへ適用した。零環を含む環比較とCharPを要するδ両立を分離し、choiceを増やしていない。新12宣言と旧利用先2件の監査、旧同型・生成元・商に関するrfl契約5件が成功。
  538対象の統合ビルド、基礎584件・B4 2,560件に加え、工程別の対象ビルドと集約focused監査が成功。
  R5/R6の旧37完全署名は変更前と一致。新sorry・追加公理・引用依存なし。

- R5c：一元添字族とのイデアル・商・完備化・標準射の比較10件を証明し、単一根の上位perfectoid性を族版へ委譲した。元の台環・標準射と一般の被約p完備終域への普遍性は保持。16入口の監査、rfl契約5件、標準射の二つの可換図式と完備化単位の比較が成功。旧6完全署名も一致。比較自体に素数性・正則性・非自明性を加えていない。
  538対象の統合ビルド、基礎584件・B4 2,560件に加え、工程別の対象ビルドと集約focused監査が成功。
  R5/R6の旧37完全署名は変更前と一致。新sorry・追加公理・引用依存なし。

- R6：環射fとW₂持上げs、projection.comp s = fを入力とする相対δ評価を共有した。仮定はp ∈ Jとx ∈ (J.comap f)^(n+1)であり、像の所属へ弱めていない。通常版は恒等射、有限段版は元の包含へ特殊化し、δ構造・有限段の台環を維持。新9宣言・移動1宣言・旧18利用先のfocused監査が成功。
  538対象の統合ビルド、基礎584件・B4 2,560件に加え、工程別の対象ビルドと集約focused監査が成功。
  R5/R6の旧37完全署名は変更前と一致。新sorry・追加公理・引用依存なし。

## 10 実装途中の再調査と並行移管の記録

この節の「残る工程」は当時の記録であり、R4c〜R6は§9のとおりコミット済み。現在の工程は§11を参照する。

2026-10-16の再調査時点ではBSは576モジュール・54,611行。
R2c/R2d/R3c/R4bの既存未コミット差分を含み、ソースimportグラフに循環はない。
534対象の統合ビルドは `RelativeFreeFiniteDeltaStep` の有限切断自然性で失敗した。
多項式切断の抽出によって、旧証明のsimpが係数・変数上の値を計算できなくなったためであり、
公開型やrflの照合だけで互換性検証を終えてはならない。
R2cでは切断自体のC/X計算を公開し、既存の自然性証明と有限段の利用先を含めて再ビルドする。
他の反映済み3工程も同じソース状態で統合監査し、工程別に保存する。

残るBS独立工程はR4c、R5a/b/c、R6、R7。
R4cは既存 `IsSMulRegular.of_flat` とG4の適用で整理し、新しい一般補題を増やさない。
R5aは未完備版の外延性を優先し、既存のPD・p完備化の外延性を再利用する。
合成標準射の外延性は実際の二つの逆写像検証に使う最小の入口とする。
R5bは同じWitt復元同型と生成元逆像を固定し、新しい表示の選択構造体を作らない。
R5cは低層比較のみ一時検証済みであり、上位特殊化・完全署名・依存監査は未完了。
R6の相対評価は§3のcomapの冪条件を維持する。これらは共通Q群を待たず進められる。

### 並行作業の更新

共通側の `TorAlgebraMilnorSequence` は実係数環に線形な元のMilnor短完全列を供給済み。
§8.4の「中央のC線形Milnor射待ち」は解消した。
`PowerTorsionTorExtension` は完備almost拡大閉性とp冪ねじれ試験のTor消滅を明示入力として、
全係数のTor零化へ接続する。これらの具体的入力とB5の実イデアル冪等性は別の数学的工程として残る。
J²零化・J零化・mod p冪像の冪等性を同一視しない。
RootTowerは既存の平坦性APIを使い、固定段からの尾部比較と明示基底・ランク・冪遷移を保持する。
DGの通常複体のK-flat性は将来候補であり、具体的な重複を確認するまでは統合しない。

共通Q群は新しい数学的入力の要求ではなく、既存証明の移管・包装候補である。
Q1/Q8/Q10、Q4〜Q7、Q2/Q3/Q9の順に担当側へ受け渡す候補とし、BS側から共通ファイルは編集しない。
Q8は指定済みの線形同型と単位を保つこと、Q4は存在と一意性の仮定を分けることを契約とする。
同じファイルを使うR2d/R5aは一人が差分を合流し、統合ビルド中はBS対象ソースを固定する。

### R7の最小範囲

予定ファイルはBS担当の `scripts/audit_bhatt_scholze_structure.py`。
Leanヘッダーの通常・public・private importを読み、循環、内部importの未解決、
明示した純基盤入口からの禁止依存を検査する。基盤入口の未指定は「未検査」と表示する。
`CommutativeAlgebra` のBS到達9モジュールはB3接続等を含むため、フォルダ全体を禁止しない。
基礎・B4・refactoring・André条件付きの監査を別集計し、B-Iの入力と互換入口も別表示する。
import被覆は証明項の依存監査ではない。公開宣言とassert_no_sorryの簡易棚卸し差分は参考警告とし、
生成宣言やnamespaceを完全解析したとは扱わない。未被覆も期待範囲を定めるまでは警告にとどめる。
循環・内部未解決・指定禁止境界の違反だけを構造検査の失敗とし、既存Lean公理監査は維持する。

共有 `audit_clmst_b3` の旧B-S sorry許可と表示は共通担当の更新候補。
証明済みB4、André条件付き、B-I、B-Rの依存境界を別々に扱う。
各工程は通常のlake設定で対象・下流のビルドと基礎/B4/追加宣言の監査を行い、
宇宙・暗黙引数・局所作用・標準射・必要なrflを保つ。ソース短縮だけでなく検証時間も確認する。


### 並行移管後の互換性確認（最終保存前）

R4c〜R6は工程別コミットを完了した。BS独立変更の538対象・4,575ジョブ、基礎584件・B4 2,560件の監査は成功済み。
その後、共通担当が根イデアル・完全係数テンソルの7モジュールを共通層へ移し、BS側をexport互換入口にした。
この並行差分を含む538対象・4,582ジョブの再ビルド、基礎584件、refactoring 169件、André条件付き監査も成功した。
旧37完全署名は `SerrePositivity.BhattScholze.compatibleRootIdeal` の正確なalias先への置換と、
表示上の空白・改行だけを対応付けると一致する。その他の名前・宇宙・引数・instanceは変更されていない。

移管後の通常のB4監査だけは、次の旧公開名のexport漏れにより584〜585行の2コマンドが失敗した。
共通側には同じ定理本体があり、数学的な未証明部分ではない。

- 対象：`SerrePositivity/BhattScholze/CompatibleRootIdealTensor.lean` の `export SerrePositivity` リスト。
- 追加する1行：`compatibleRootIdealTensorMap_tmul`（`compatibleRootIdealTensorMap` の直後）。
- このaliasだけを一時的な監査ファイルへ加えたB4全2,560件の検査は成功し、標準3公理のみ。
- 並行作業の対象ファイルは編集・ステージしていない。担当チャットへの修正依頼は、元のユーザー指定に従って送信許可を確認中。

移管前の成功、移管後の通常監査の未解消、修正案を含む一時監査の成功を区別する。
最終集計R7は、この旧名の互換性が担当側で復旧した後に確定する。


## 11 今回の調査を反映した次期実施計画（2026-10-16）

ユーザーのgoal継続指示により、読み取り調査の結果を保存し、BS側で独立して進められる部分を実施する。
今回の開始時HEADは `23e89923`。BSは579モジュール、約5.4万行で、R1〜R6は既に実装・個別コミット済み。
調査対象の全ソースimportグラフに循環はなく、明示した5つの基盤入口からの禁止依存もなかった。
これはLeanビルドや証明項の公理監査の代わりではない。

### 11.1 担当と現状の確定

BS担当は本計画、BS専用監査、下記N1/N2のBSファイルを編集する。
共通CA/HA、CLMST、RootTower、DG・ホモトピー基盤、ルートimport、共有監査は変更しない。
並行移管中のBS互換入口7ファイルも移管担当の差分として保持し、BS独立変更へ混ぜない。

移管7ファイルは現在Batteriesの `alias` による実宣言の互換入口へ変わった。
旧31名のうち `compatibleRootIdealTensorMap_tmul` のみが未列挙で、共通側の本体は存在する。
復旧は移管担当の範囲。過去のexport版のビルド・完全署名比較を、現在のalias版の検証と同一視しない。
移管側のソース確定後、旧31名、完全型、標準射、rfl/simp契約、通常B4監査を再確認する。
他チャットへの新たな送信は行わない。

共有 `audit_clmst_b3.lean` は旧B-S宣言をsorry許可リストに残し、B-Sが未証明とする表示を持つ。
宣言への到達とsorry依存を区別する更新は共通担当が行う。B-I/B6・André・B-Rの引用境界は維持する。

### 11.2 BS側で独立して実施する工程

| ID | 対象 | 契約と分類 | 状態 |
| --- | --- | --- | --- |
| N0 | 本計画 | 現在地、担当、共通化候補、検証・保存の順序を記録 | `54f3d966`で保存済み |
| N1 | `CompatibleRootFamilyQuotient.lean` | 被約なp進完備終域への一意延長を一般入口に抽出。旧perfectoid入口を同じ型の包装にする。仮定弱化を伴う証明拡張 | 実装・境界例・旧7型一致・172件のfocused監査済み |
| N1a | `CompatibleRootSingletonComparison.lean` | 並行alias移管後の二つのイデアル一致証明を、元のspan表示への明示的changeで修復。型・同型・標準射は維持 | 修復・下流ビルド・既存169件のfocused監査済み |
| N2 | `CompatibleRootPDComparison.lean`、`CompatibleRootFamilyPDComparison.lean` | 同じ完備化環上のpイデアル像の計算を既存 `pIdeal_map` へ置換。新宣言・import・instanceなし | 実装・旧4型一致・176件のfocused監査済み |
| N3 | `scripts/audit_bhatt_scholze_structure.py`、BS専用監査 | 引用・共有監査掲載・aliasの参照分類を追加。ソース解析をLeanの証明監査と区別する | 実装・自己テスト11件・11基盤入口検査済み |

N1の新公開名は `existsUnique_compatibleRootFamilyCompletionLift` とする。
任意の `p : ℕ`、`ρ : σ → ℕ → R`、`hρ : ∀ s n, ρ s (n+1)^p = ρ s n`、
被約かつ `span {(p:T)}` について古典的完備なT、
`g : R / compatibleRootFamilyZeroIdeal ρ →+* T` を入力とし、
`∃! l : CompatibleRootFamilyCompletion p ρ →+* T,
 l.comp (compatibleRootFamilyCompletionMap p ρ) = g` を結論する。
新入口にはp素数・Rのperfectoid性・有限性・添字の非空性を要求しない。
元の商・完備化・標準射を変更せず、非素数p、空族、零環、旧公開型とrflを監査する。
単一版を任意族版へ全面的に委譲すると現在のimportが循環するので、その依存反転は行わない。

N2は二つの `hm` の証明のみを `pIdeal_map Q (AdicCompletion I Q) p (algebraMap Q _)` に置換する。
既存の `IsAdicComplete.map_algebraMap_iff` と完備化自身の完備性を再利用し、汎用APIを新設しない。

N3の調査時の参照差分13件は、引用関連6件と共有 `audit_clmst_b3` に掲載済みの7件。
別にalias等のためソース宣言として未解析のassert名31件がある。未証明件数とは扱わない。
共有監査は読み取りの参照だけとし、専用監査の被覆や成功件数へ合算しない。
名前・importからの分類は証明依存を保証しないため、曖昧なものは未分類として残す。
旧公開名の完全性は現ソースのリストだけから判定せず、移管前の31名を基準にLean環境で検証する。

### 11.3 共通担当と調整する抽出候補

Q1〜Q10の最小契約は既存証明の包装・抽出であり、B4用Gの未到着として扱わない。
優先はQ1・Q8・Q10、続いて二段延長とQ7・Q4〜Q6、その後Q2・Q3・Q9。

| 項目 | 現在の契約・配置案 | BSで残す内容 |
| --- | --- | --- |
| Q1 | CA `CompletelyFlatCriterion`。標準商のTor消滅と同じextendScalarsの忠実平坦性から完全忠実平坦性。正則性・FG・完備性不要 | prism/PD/根付き拡大の実入力供給 |
| Q8 | HA `DerivedCompletion/ReflectionRing`。反射性、完備なR代数T、指定済み線形同型EとE(e)=1から、順射が同じEの代数同型 | 選択済み同型、実H0・標準単位の照合 |
| Q10 | CA `PerfectoidizationFunctor`。hfと源同型eからIsPerfectoidization p (f.comp e.toRingHom)。同じuniverse | 実際の核商・生成族商の同型と全射性 |
| Q4 | CA `AdicCompletionExt`近傍。I.map f≤Jによる環射延長。存在にはI.FG不要、一意性にはI.FGとJ分離性 | δ両立性と具体的剰余公式 |
| Q5 | HA `DerivedCompletion`の閉性。導来完備Mの1−bL全単射、a,b完備からa+b完備、aⁿ完備からa完備(n≠0) | Frobenius公式への適用 |
| Q6 | HA `DerivedCompletion`。実Λ_dΛ_f(single R)のH0反射性と合成単位。通常H0環の反復とは比較で接続 | 根raw環とδ完全化環への具体化 |
| Q7 | HA `DerivedCompletion/RestrictionCompletion`近傍。二段係数制限比較と合成単位の等式。実導来圏版とMinus版を分ける | 元の係数射と像の具体式、H0作用 |
| Q2 | HAの商加群colimit。Preorder＋OrderBot、単調K、全射β、kerβ=⨆Kから元の評価先を頂点とするIsColimit | 有限関係式・核・局所Algebra作用の計算 |
| Q3 | CAの正則族入口。各有限S外のf(s)の商上正則性からnodupリストの弱正則性。Nontrivial不要 | 根関係式の正則性。独立したprefix重複は現在2件 |
| Q9 | HA `DerivedCompletion`。正則d、上有界X、d完備、全正冪還元の負次数消滅からIsGE 0 | IsLE 0、離散性・平坦性の追加入力 |

追加候補：二段実導来完備化のHom同値。
任意 `X Y : DerivedCategory.Minus (ModuleCat A)`、Yのa・b導来完備性から
`Hom(Λ_b Λ_a X,Y) ≃ Hom(X,Y)` を既存 `derivedComplexCompletionHomEquiv` の二回適用で包装する。
順方向は元の合成単位との前合成、逆方向は既存逆写像の合成とする。
共通側の予定配置はHA `DerivedCompletion` の反射性API近傍（担当調整後にファイルを確定）。
BSの `DeltaRootSourceCandidateCompletion`、`DeltaRootSourceCandidateFactorization`、
`DeltaAlgebraPerfectionPDCompletionMap` は具体的対象への特殊化を担当する。
δ非依存の汎用版をBSへ二重実装しない。

### 11.4 到着中APIの利用と並行数学の境界

この節の調査時には未コミットだった `FiniteSupQuotientColimit` は、Finset σ上の有限イデアル和の商と頂点R/⨆Iを扱う。
受渡し検証後、BSの `DeltaDivisionEvaluationFiniteSupportColimit` に適用できる。
まず各段K(S)=S.sup(I_z)、次に核商から元のβ作用付き評価先への同型、最後に遷移射・評価射の公式を証明する。
ℕ図式の二つの評価余極限をそのまま置換せず、一般Q2または図式比較を別に用意する。
当時は受渡し待ちの接続候補としてN1〜N3の開始条件にしなかった。現在は保存済みであり、§12のN4で適用を評価する。

有限根族・任意根族・完全環の根基商/全射の全正次数Tor消滅も当時は実装中だったが、現在は保存済みである。
BSで同じ有限族帰納法や商余極限を作り直さない。新ソースの存在と検証済み公開APIを区別する。
RootTowerはcofinal tail、明示基底・ランク・冪遷移を保持する。
DGの通常複体K-flat性は具体的な重複と担当契約を確認してから検討し、相対DG作用と全Hom自然性は残す。

B5の具体的完備導来乗法の同型性hμは新しい数学として別工程。
通常商B/Iと選んだperfectoid商をB4と核の一致で同定し、元の実乗法・完備化の図式を保つ。
共通 `CompletedQuotientTensorExtension` のhμから拡大閉性・全mod pⁿ像の冪等性への含意は再証明しない。
CLMSTの完備塔上の実p冪ねじれTor入力も別に必要で、既存の移送定理だけで供給済みとはしない。
B-I/B6、André条件付き入力、残るCLMST引用は維持する。

### 11.5 検証と保存の順序

1. N0を文書単独で差分確認してコミットする。
2. N1/N2は別ファイルで実装し、各公開型・具体的標準射・必要なrfl/simpを保つ。
3. 各工程の対象と下流を通常lake設定でビルドし、focused公理監査を行ってから個別コミットする。
4. N3は分類・alias・コメント等の自己テストと実ソースの構造検査を行う。これはLean検証とは別記する。
5. ソースを固定して基礎・B4・refactoring・André条件付きの統合監査を行う。
   並行移管の旧名漏れが残ればその失敗を明示し、監査を弱めたり共有ファイルを修正して通したりしない。
6. 自分のファイルだけを明示的にステージする。実施済みと受渡し待ちを記録し、未検証項目を完了にしない。

大規模な型クラス化、既存δ構造の再定義、全ファイルの再配置、局所instanceのglobal化は行わない。
二〜三行の既存API適用だけになった残余比較を、大きなデータ構造へ包み直す工程も採用しない。


### 11.6 次期工程の実施記録

- N3：共有監査の掲載先と、引用元モジュール／引用import到達／未分類を参照情報として分けた。
  `alias` は通常宣言と別のソース候補として表示し、元の宣言集計と専用監査被覆を維持した。
  共有監査を成功件数や専用被覆に加算せず、証明項の依存やLeanの名前解決成功とも同一視しない。
  自己テスト11件、実ソース構造検査、明示した11基盤入口の禁止依存検査、差分検査が成功。
  別レビューでも既存の構造判定・終了コード条件が維持されていることを確認した。
  N1の監査追記前の状態では未掲載候補14件（共有参照7、引用元2、引用import到達4、新N1入口1）。
  旧assert名31件のうち30件はソースalias候補に一致し、tmul旧名1件は照合未解決。
  後者を未証明と呼ばず、並行移管の互換性問題として引き続き扱う。


- N1a：並行alias移管後、単一根・一元添字族のイデアル一致の二証明が失敗した。
  旧名の一段unfoldに依存せず、同じspan表示への `change` を明示して修復した。
  比較同型・標準射・公開型は変更せず、専用監査のR5c節もBS名前空間内に置いて名前の曖昧性を除いた。
  最初の統合ビルドの失敗は成功扱いにせず、修復後の下流4,299ジョブ、
  BS専用監査の全536入口・4,582ジョブ、既存169件のrefactoring監査の終了コード0を確認した。
  ビルド中のBSソースハッシュ変化なし。既存の単一根比較のrfl・標準射図式も監査に含む。
  通常B4監査は移管側の `compatibleRootIdealTensorMap_tmul` 不足による2コマンドだけが失敗。
  この別件を修復済みと数えず、共通移管ファイルや監査の対象宣言を変更していない。


- N1：`existsUnique_compatibleRootFamilyCompletionLift` を任意の自然数pについて証明した。
  終域の被約性・古典的p進完備性を明示し、旧perfectoid入口は同じ型の包装として保持した。
  元の商・完備化・標準射の定義は不変。根の消去と完備化延長は既存APIを使い、新引用・公理・instanceなし。
  旧7宣言の完全署名はbaselineビルド後の取得と変更後でbyte一致。
  一般p、空添字族、非素数p=4と非零終域ZMod 2、p=0と終域ℤ、任意pでの零源・零終域、
  既存台環と標準射・代表元公式のrfl 4件を検証した。
  境界監査初版の両名前空間openによる曖昧性は監査側で修正し、修正後に終了コード0を確認した。
  536対象・4,582ジョブの統合ビルドと基礎584件が成功。追加3入口を含むfocused172件も終了コード0、標準3公理のみ。
  通常B4監査の移管側旧名1件の不足は別件として残り、成功と報告しない。


- N2：単一根・任意根族のp完備化の自己作用について、二つのイデアル像の計算を既存 `pIdeal_map` へ置換。
  新しい定義・import・instanceを増やさず、`omit [Fact p.Prime]` と元の完備化を保持した。
  元HEADの二ファイルを一時ファイルで再elaborateして取得した4完全署名と、
  最新importからの署名は表示空白・改行のみの正規化で一致した。
  536対象・4,582ジョブの統合ビルド、4入口のfocused依存監査、追加後の集約176件が終了コード0。
  依存公理は標準3公理のみ。新sorry・外部引用なし。

## 12 再調査後の実施計画と受入条件（2026-10-16）

直前の読み取り調査はHEAD `e93e3bdb`まで、実装再開時は`9aefab1c`。
ユーザーのgoal継続指示に従い、まず調査結果を文書化し、BS側で独立して進められる部分を実施する。
読み取り調査時のBSは579 Leanファイル・54,387行。直近の536対象の統合ビルド時と全579ソースのhashが一致した。
構造監査は循環なし、指定13基盤入口の禁止依存なし。これは今回の新しいLean検証の成功とは区別する。
R1〜R6とN1/N1a/N2/N3は実施済みで、今回の新規成果として再計上しない。
N1は`adfb4fbf`、N1aは`e46e061b`、N2は`f844826e`、N3は`82e78338`で保存済み。

### 12.1 担当と現在の互換性問題

編集対象はこの計画、以下のN4/N5のBSモジュール、BS専用監査のみ。
共通CA/HA、CLMST、RootTower、DG・ホモトピー、ルートimport、共有監査を変更しない。
移管担当のBS互換入口7ファイル（CompatibleRootIdeal、CompatibleRootFamilyIdeal、CompatibleRootIdealFlat、
CompatibleRootIdealTensor、CompatibleRootPerfectQuotient、CompatibleRootQuotientTor、PerfectCoefficientTensor）も変更しない。
他チャットへの送信は行わない。

`25e22daa`で七ファイルの共通移管と有限根族・任意根族・完全環根基商/全射のTor消滅が保存された。
移管前の旧公開名31件に対しaliasは30件で、`compatibleRootIdealTensorMap_tmul`の旧BS名だけが欠ける。
共通の元定理はCA/CompatibleRootIdealTensorに存在する。復旧は移管担当が行う。
移管後の30件の一覧を互換性基準にせず、旧31件の環境内宣言・完全型・属性・rfl/rw/simp契約を基準にする。
通常B4監査は旧名を使う2コマンドで失敗しており、全体ビルド成功とは別の結果として保持する。
この不足を一時監査で補った成功は通常監査の成功としない。BS独立作業は進め、統合受入は復旧後に行う。

### 12.2 BS独立工程：N5を先行し、N4を採否判定付きで実施する

| ID | 予定ファイル・担当 | 内容・終了条件 | 初期状態 |
| --- | --- | --- | --- |
| N5 | BS担当：PerfectPrismRootSourceDiscrete、PerfectPrismDeltaAlgebraDiscrete | 既存Milnor零化定理のr=s=1によって二つのholim消滅証明を短縮。実対象・再構成・公開型・正規化single比較を保持 | 計画のみ、Lean置換後未検証 |
| N4 | BS担当：DeltaDivisionEvaluationFiniteSupportColimit | 共通有限和商colimitへの比較で旧余極限性を委譲。旧9公開宣言の型、元の図式・局所作用・標準射と必要なrflを保持 | 共通API保存済み、BS接続未実施 |
| N6候補 | BS担当：SecondCoefficientPowerEquiv等の性能記録 | 重い型照合の測定を先行。既存同型・係数/変数公式を保つ改善が確認できる場合だけ別工程を立てる | 未測定の設計候補、コード変更は未採用 |

N5では、既存 `complexTowerHomotopyLimit_homology_annihilated` にr=s=1を適用する。
隣接するiとi−1での零性は各ファイルの `powerCokernel_homology_isZero` から供給し、1作用の零性からholimのIsZeroを得る。
旧hs（差分写像の全射性）→hinj（Milnor射の単射性）→hzの重複だけを置換する。
同じchosen model、項の平坦性、正則性からの有界ねじれ、完備性、powerCokernelReconstruction、
実対象への同型輸送、IsLE 0の独立証明は維持する。一般Q9はBSへ新設しない。
既存MilnorAnnihilatorを直接importし、BS2ファイル以外の本体を編集しない。

N4の具体的対象を固定する。
L=RelativeFreeDeltaRing (R:=A) σ、β=deltaDivisionSourceEval D a、
g(z)=deltaDivisionSourceGraphRelation D a z、J(z)=Ideal.span {g(z)}、
K(S)=deltaDivisionEvaluationFiniteSupportIdeal D a Sとする。
まずK(S)=S.sup J、ker β=⨆z,J(z)、核商から元のβ作用付きAへのL線形同型を比較する。
`Ideal.span_range_eq_iSup`、`Submodule.quotEquivOfEq`等を再利用し、同等の一般イデアル補題を新設しない。
元のtransition・ModuleDiagram・eval・EvalCoconeの定義を保持し、自然同型と余錐比較によって
`finiteSupQuotient_isColimit`を旧 `deltaDivisionFiniteSupportEvalIsColimit` へ運ぶ。
K(S)=S.sup Jは命題的一致であり、図式をabbrevで置換して旧rflを失わない。
IsColimitはdescを含むデータなので、そこから作る同型の定義的一致を無条件に主張せず、
全段ι公式とhom_extで標準射の一致を確認する。
直接下流のBoundedSupportColimitと任意根族のTor入口まで検査する。
空族・空有限集合・零環を保持し、有限性・非空性・非自明性・遷移単射性を追加しない。

N4の目的は、独立保守されるdesc/fac/uniq証明を共通層へ一本化すること。
比較層が型照合や保守を悪化させる場合は採用せず、具体的な試行結果を記録して一般Q2へ繰り越す。
ソース行数だけでは採否を判断しない。ℕ添字の二つの評価余極限はこの工程で変更しない。

### 12.3 共通抽出の再優先付け

共通抽出は担当調整後に共通側が実装し、BS側は受領した公開APIを具体的入力へ適用する。
同等の汎用版をBSに二重実装しない。Q群はG群の未到着入力ではなく、既存証明の整理候補である。

| 候補 | 優先度と現在の理由 | 最小契約で維持する点 |
| --- | --- | --- |
| Q1 | 高。BS5箇所の完全忠実平坦性の包装 | 標準商のTor消滅と同じextendScalarsの忠実平坦性。正則性・FG・完備性不要 |
| Q8 | 高。BS1箇所、共通2箇所 | 指定した線形同型E、E(e)=1、終域完備性から同じEの代数同型。終域側反射性・新choice不要 |
| Q10 | 高・小規模。BS2箇所 | hfと源同型eからf.comp eのIsPerfectoidization。同じC・f・universe |
| 二段Hom同値 | 中。BS3箇所 | Yのa,b導来完備性からHom(Λ_bΛ_a X,Y)≃Hom(X,Y)。合成単位と既存逆射を保持 |
| Q7 | 中。既存G8の二回適用 | 元の係数射、像、合成単位。実導来圏とMinusの版を区別 |
| Q4 | 中。BSと共通p完備化の延長が重複 | I.map f≤J。存在には終域J完備性、一意性にはI.FGとJ分離性。δ両立性はBSに残す |
| Q2 | N4の結果を受けて判断 | Preorder+OrderBot、単調部分加群K、全射β、kerβ=⨆Kから元のNを頂点とする評価余錐。有限和商版と区別 |
| Q3 | 中低。独立prefix証明は現在2件 | 有限集合外の元の商上正則性からnodupリストの弱正則性。Nontrivial不要 |
| Q5 | 低へ変更。現在は単一実装の所属整理 | Neumann型全単射、和、非零冪からの導来完備性。既存倍数閉性を再利用 |
| Q6 | 低〜中へ変更。既存単一証明の移管 | 実Λ_dΛ_f(single R)のH0と単位。通常H0環の反復との比較を保持 |
| Q9 | 汎用抽出は低へ変更。先にN5 | 正則d・上有界X・d完備・全正冪還元の負次数消滅からIsGE 0。IsLE・平坦性は別 |

二段Hom同値の一般入口は既存の実導来圏版HomEquivを合成でき、Xの完備性・上有界性・正則性は不要。
BSの実利用ではMinusの対象を忘却して使い、公開されている中間p段の射を保持する。
任意有限列の完備化体系への拡大、大規模な型クラス化、既存DeltaStructureの再定義、全ファイル再配置は採用しない。

### 12.4 並行作業と新しい数学の境界

`e93e3bdb`の自由完全多項式代数の評価・全射表示・普遍性に続き、再開時には`9aefab1c`で基底上平坦性も保存された。
一般の完全環図式のTor独立性は共通担当が進めており、ソースの出現・検証・保存を区別して受領する。
BS側で自由完全代数や同じTor証明を作り直さない。
B5ではB4と核一致で通常商を選んだperfectoid商へ同定し、実完備導来乗法の同型性hμを供給する。
共通CompletedQuotientTensorExtensionのhμから拡大閉性・全mod pⁿ像の冪等性への含意は再証明しない。
H0同型だけではhμを満たさない。CLMST固有のp冪ねじれ試験加群上のTor零化も別入力である。
これらの新証明を今回のリファクタリングに含めず、B-I/B6とAndré条件付き入力を維持する。

RootTowerでは一般余極限平坦性を利用できても、各段A_n上のcofinal tail比較・明示基底・ランク・冪遷移は残す。
DGの相対作用・全Hom自然性・coherence、ホモトピーのbar/resolution比較をBS導来完備化へ組み込まない。
通常複体のK-flat性の具体的な重複は今回確認できず、共通化は二つの実利用が確認されてから検討する。
CA/PerfectoidIdealのようなB3への接続層と純基盤を区別し、フォルダ全体に一律のBS禁止規則を課さない。

### 12.5 検証・保存・文書の受入

1. 本節を文書単独で保存する。
2. 変更前の完全型と必要な計算契約を取得し、N5、次いでN4を別の検証・保存単位として扱う。
3. 各工程で通常lake設定の対象・下流ビルド、assert_no_sorryと公理依存、旧型・標準射を検査する。
   通常B4の既知の互換名不足は別件として明示し、監査対象を減らして成功扱いにしない。
4. 統合検証ではソースhashと対象一覧を記録し、ビルド中の変更を確認する。
   プロセスの観察timeoutを終了と扱わず、同じ実行handleを追跡する。
5. 自分の検証済みファイルだけをパス指定でコミットする。他作業のstaged/untrackedファイルを含めない。
6. 実装・検証・保存・受渡し待ちを分けて本節へ記録する。

共有audit_clmst_b3の古いB-S sorry許可と表示の更新は共通担当の候補として残す。
名前到達、sorryへの証明依存、import被覆、実際の監査成功を区別する。
公開型は宇宙・暗黙引数・局所Algebraを含み、既存rflと射の命題的一致を別々に確認する。
性能候補は同じ通常設定で計測し、上限増加だけを改善としない。
