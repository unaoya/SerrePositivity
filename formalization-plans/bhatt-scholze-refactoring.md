# Bhatt–Scholze 形式化のリファクタリング計画

作成日：2026-10-16。BSの証明済み構成を保ち、既存APIの再利用、一般補題の配置修正、重複証明の統合を順に行う。
原典証明の正本は[BS計画](bhatt-scholze.md)、担当・待合せ・合流の正本は[CLMST計画 §0.2](clmst.md)とする。
この計画は証明経路や引用範囲を変更しない。B3の存在・普遍性、B4の一般全射性を維持し、B5の新しい数学とは分ける。

§8の再調査は、ユーザーの「コードを書き換えない」という指定に従い、計画書のみを更新した記録である。
その後の目標継続指示により、この計画に沿うBS独立部分の実装・検証・個別コミットを再開する。
共通担当のファイルは変更せず、既存の未コミット差分を先に検証・保存する。
状態表と§9の実施記録を優先し、§1・§7・§8の件数と検証記録は各実施時点の記録として読む。

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
| R2b | 環同型によるδ構造移送を統一 | 抽出 | 新 `DeltaTransport`、`DeltaDivisionSourceTensorDelta`、`DeltaRootSourceRawH0Delta` | 反映・対象ビルド済み、統合監査・保存待ち |
| R2c | 変数のδ値を指定する多項式構成とδ射判定 | 抽出 | 新 `PolynomialDelta`、`RelativeFreeDelta`、`PolynomialRankOneDelta`、普遍性利用先 | 6モジュールの一時試作を検査済み、repo未反映 |
| R2d | 有向環余極限上のδ構造と普遍射 | 抽出 | 新 `DeltaDirectLimit`、`DeltaPerfection`、`DeltaPerfectionUniversal`、`DeltaAdjoinDivisionFiniteColimit` | 一時ファイルで構成を検証中、repo未反映 |
| R2e | δ閉包の生成元定理を基礎層へ集約 | 配置・再利用 | `DeltaClosureGeneration`、`DeltaDivisionIteratedRelations` | 反映・対象ビルド済み、統合監査・保存待ち |
| R3a | rank-one DPの一般比較射を分離し特殊版を一般版へ委譲 | 配置・再利用 | 新 `RankOneDPBaseChangeMap`、`RankOneDPTensorRelations`、`RankOneDPAnyBasis`、`RankOneDPPrimeBasis`、`RankOneDPBaseChange` | 完了 |
| R3b | principal DPの一般関係式を分離し基底変更を一本化 | 配置・再利用 | 新 `PrincipalDPBaseChangeRelations`、`PrincipalDPBaseChange`、`PrincipalDPBaseChangeUniversal` | 反映・対象ビルド済み、統合監査・保存待ち |
| R3c | DP表示の正則性で不要なp局所性を外した一般入口 | 証明拡張 | `PrincipalDPRegular` | 一時試作を検査済み、repo未反映 |
| R4a | 初期係数表示を既存モニック表示比較へ接続 | 再利用・比較 | `DeltaDivisionFirstCoefficientPowerEquiv`、`MonicPowerFamilyBaseQuotient` | 旧同型を保つ案を反映・対象ビルド済み、統合監査・保存待ち |
| R4b | 根関係式の通常の冪指数を非零指数に一般化 | 証明拡張 | 新 `MonicPowerFamilyRelationRegularity`、`DeltaRootRelationKoszul`、`DeltaRootSubsetQuotient`、`DeltaRootFiniteRegularSequence`、`DeltaDivisionSourceGraphKoszul` | 一般補題単体の一時検査済み、利用先は未検証・repo未反映 |
| R4c | hpAからhpL・ghost単射を供給する公開入口を揃える | API整理 | `DeltaDivision*`、既存G4利用箇所 | 未着手 |
| R5a | 未完備perfection・合成標準射のhom_extと既存PD外延性の適用 | 抽出 | `DeltaPerfectionUniversal`、`DeltaPerfectionPDCompletionUniversal`、`DeltaPerfectionPDCompletionComparison` | 一時ファイルで構成を検証中、repo未反映 |
| R5b | 完全prismのWitt表示とイデアル像の入力供給 | 抽出 | `PerfectPrismHomLift`、`PerfectPrismQuotientPerfectoid`等 | 未着手 |
| R5c | 単一根の上位perfectoid証明を任意族から特殊化 | 比較 | `CompatibleRootCompletionPerfectoid`、族版 | 依存循環を確認して実施 |
| R6 | 相対δのイデアル冪評価・剰余算術を共有 | 証明拡張 | `DeltaAdicEstimate`、`RelativeFreeFiniteDeltaAdicEstimate`、剰余計算 | R2後に契約を再確認 |
| R7 | BS監査の宣言列挙・公開境界検査、文書の現況整理 | 監査・文書 | BS専用スクリプト、BS計画 | 各工程と並行 |

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
`Ring.DirectLimit.hom_ext` による非空性・有向性の仮定削減は未検証の候補であり、現構成の抽出と分ける。

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
   `hom_ext` による非空性・有向性の仮定削減は、構成の抽出後の別単位とする。
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
