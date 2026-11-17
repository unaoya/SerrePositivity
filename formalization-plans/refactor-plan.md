# 論文の層の整理計画（2026-10-30）

概要：論文の層（`SerrePositivity/` のうち BhattScholze・∞ 圏の基盤を除く部分と、CLMST）について、ファイルの統合、死んだファイル・未使用の
宣言の削除、Mathlib への置き換え、重複の一本化、層の順序の修正、Mathlib への提出候補を一つにまとめた計画。前半（A〜H）が全体の方針と順序、
後半（第 1〜11 章）がディレクトリごとの詳細。ディレクトリごとの調査（2026-10-29〜30、読むだけ）の結果を元にしている。
方針：群ごとに提案 → ユーザーの承認 → 実装 → 新しいファイル単体と直接の利用先のビルド → 区切りで全依存ビルドと監査 → コミット。
規約：Mathlib の確認は固定版（2026-10-07、`.lake/packages/mathlib`）と最新版（2026-10-28、`/tmp/mathlib-latest`）の両方で行った。
提出候補は [mathlib-upstream.md](mathlib-upstream.md) の G 番号の表に移してから扱う。この文書だけで作業が再開できるように書く
（以前のディレクトリごとの計画書は `archive/` に移した）。
使われ方：作業を再開するときの手順書。群に着手する前に該当する章を読み直し、宣言の利用状況をもう一度確かめる。

## A. 作業の決まり

- ビルド：群ごとには新しいファイル単体と直接の利用先だけをビルドする。全依存ビルドは複数の群をまとめて一回にし、通るまでコミットしない
  （全依存の半分は BhattScholze の重いモジュール）。新しいファイルの確認は `lake build` で行う（module のファイルに `lake env lean` は使わない）。
- 群ごとの確認ビルドの範囲（2026-10-30）：新しいファイル単体（組み立ての誤りを早く拾う）と、論文の層の直接の利用先だけ。BS/CLMST・∞ 側の
  importer は import 行と参照の機械的な書き換えなので、区切りの最後の全依存ビルドに任せる。論文の層の確認ビルドは数群ぶんまとめて 1 回にする。
  下の層の docstring だけの手直しは、下流の再ビルドを起こすので区切りの最後にまとめる。
  ただし定義や宣言の中身を変える群（置き換え・改名・定義の差し替え）は、変えた名前を実際に使うファイル（BS/CLMST を含む）だけを群の中でビルドして確かめる。
- BhattScholze/・CLMST/（別セッションの管轄）：モジュールの統合・改名に伴う import 行の書き換えと、改名・削除した宣言の参照の書き換えは
  行ってよい。証明の中身は変えない。BS/CLMST 分は独立したコミットにし、旧→新の対応表をメッセージに書く。例外として、BS の作業時間（E）には
  コーディネータが BhattScholze/ にファイルを置く・移す（IteratedTensor*、CLMST の BS 依存の基礎、CA の BS 依存のもの）。
- 監査：`scripts/audit/*.lean` は `python3 scripts/make_area_audits.py` で生成する（手編集しない）。dg・bhatt_scholze の差分が並行セッション
  由来なら checkout で戻す。`scripts/audit_local_algebra.lean`・`audit_clmst*.lean`・`audit_f*.lean`・`audit_axioms.lean` などは宣言名を
  直接書いているので、削除・改名のたびに直す。全依存ビルドの後に shared（sorryAx は許可された引用経由の 59）・clmst・bhatt_scholze・
  audit_clmst・audit_f4・audit_f5・audit_local_algebra・audit_axioms を流す。
- 論文の内容は残す：論文の番号付きの主張と、論文の議論の変種は、主経路で使われていなくても残す（2026-10-30 の決定。CLMST の Thm 4.0.3(a)、
  Paper の Theorem4_7・Corollary2_6・Lemma3_4・Lemma2_4・ParameterQuotientCM・FlatRealization）。消すのは、置き換えられた古い証明の経路、
  論文にない死んだ補助、再エクスポートの殻。
- 宣言名：BS/CLMST が多数参照する中心の宣言（各章の「変えない名前」）は改名しない。必要なら `@[deprecated] alias` を経由する。
- 好み：`.choose` より `def` と `@[simp]` 補題。薄い包みは利用が多いときだけ残す。名前空間はファイル名から付けない。docstring は
  概要／方針／規約／使われ方。
- 統合の手順：旧ファイルは `git show HEAD:` か作業木から読み、`section` で包んで新しいファイルに組み立てる（モジュールの docstring がない
  ファイルに注意）。旧→新の対応で import のグラフを縮約して閉路を調べてから import 行を一括で書き換える。`@[expose]` の有無は元のファイルに
  合わせる（`@[expose]` で証明が止まることがある）。
- 順序の正本：作業の順序は E が正本。各章の「順序」の節は章の中の作業順だけを示す（E と食い違うときは E に従う）。
- 区切り：E の段階は「区切り」の単位で進める。1 区切り＝提案・承認 → 実装 → 全依存ビルド 1 回 → 監査 → コミット。区切りを閉じる条件：
  全依存ビルドが通る、shared の sorryAx が許可された引用経由の 59 から増えない、audit_axioms で主定理の公理が変わらない、消した・改名した
  宣言を監査が参照していない、ファイル数と行数の前後を記録する（F）。
- 提出候補の転記：区切りを閉じるたびに、その区切りで扱った章の「提出候補」を mathlib-upstream.md の G 番号の表へ移す。
- ∞ 基盤との境界：区切りに入る前に、触るファイルと ∞ 基盤の側（[handover-ct-to-infinity-2026-10-30.md](archive/stage-i/handover-ct-to-infinity-2026-10-30.md) の対象、
  InfinityCategories・HomotopicalAlgebra・KST・EInfinity・Spectra・DifferentialGraded）が import し合っていないかを確かめ、あれば先に伝える。
- コミットとプッシュ：`git commit --only` か慎重な stage。広い `git add SerrePositivity` はしない。並行セッションの未追跡ファイル・exposition/
  の変更は含めない。プッシュはユーザーの判断。

## B. 層の順序

目標とする順序（下から）：

```
Mathlib
 → CategoryTheory
 → CommutativeAlgebra（BhattScholze に依存しない部分）
 → HomologicalAlgebra
 → LengthAlgebra の核（正規化長さ λ。今の PerfectComplex/NormalizedLength ほか）
 → PerfectComplex
 → LengthAlgebra（残り）
 → KTheory
 → IntersectionMultiplicity
 → Asymptotic
 → BhattScholze（CA の perfectoid 部分・CLMST の BS 依存の基礎を含む）
 → CLMST
 → Paper
```

今この順序に逆らっている依存と、その解き方：

| 逆らっている依存 | 解き方 | 章 |
| --- | --- | --- |
| CT → HA（ScalarSupport → NullHomotopy、TruncationTriangle → StupidTruncation） | 一般の補題 2 つを CT へ。StupidTruncation は Mathlib を上げるまで保留 | §1.2.1 |
| CT の Nerve*・Simplex/Chains ↔ HomotopicalAlgebra/Simplicial | ∞ 基盤の側で Nerve 9 本を HomotopicalAlgebra/Simplicial へ移す（R76） | §1.3・G の 4 |
| HA/ComplexLimits/*（3 本）→ KST（名前空間は EInfinity） | ∞ 基盤の側へ渡した（伝達文 §5） | §3.2.1 |
| CA → BhattScholze（PerfectoidIdeal 系・AbsolutelyIntegrallyClosedPerfectoidQuotient・MonicRelationRegularSequence ほか） | BS 側へ移す（E の作業時間） | §2.8・§8.2.2 |
| CA/Koszul/RegularEuler → IM.ResolutionEvaluation | ResolutionEvaluation の前半（`chiLam`・`chiOrd`）を PC へ、`chi` を下ろす | §5.2 |
| CA/KoszulMultiplicity/Formula → LA.ConeCompositionEuler（`lambdaEuler_scalarCone_pow`） | ConeCompositionEuler の λ の錐の補題を LA の核へ | §5.2 |
| LA ↔ PC の入り組み（PC/NormalizedEuler → LA.ExactSequenceEuler → LA.SerreQuotient → PC.NormalizedLength） | 正規化長さと Serre 商の核を LA の核として PC の下へ | §5.2・§4.2.1 |
| PC ↔ KTheory の相互依存 | PC を下に。`PerfectModuleResolution`・`mk_shift` を PC へ、IntegerEuler 系・Adams の Koszul・FiniteProjectiveResolutions を KTheory へ | §4.5.1・§6.2.5 |
| PC/TensorTorComparison → IM.Basic | `chi`（50 行）を HA/Tor の近くへ | §5.2 |
| BS/Almost/PerfectoidAlmost → CLMST.Almost、Paper/Section2/MixedPerfectoid → CLMST.Algebra | Almost・MixedPerfectoid を BS 側へ | §8.5 |
| DifferentialGraded/Verdier/OrderSquare → Asymptotic（ビルドされない連鎖） | ∞ 基盤の側（DifferentialGraded）の整理で扱う | §7.1 |
| CA/Perfectoidization → Inputs/Perfectoidization → BhattScholze | CA/Perfectoidization を BS 側へ（区切り 2a） | §11.1・§2.8 |
| Inputs/CLMST → Paper/Section2/*、IM/Additivity → Inputs/IntersectionTheory → IM/AdamsVanishingAll | Inputs の包みを解体 | §11.1 |
| CT/EulerComparison → GroupTheory/ConjugateSum | 改名して EulerComparison へ吸収 | §11.2 |

## C. 名前の規約（全章に共通）

- 論文の番号・出典を名前に使わない：名前空間 `Section2`（LA の RootTowerLength、CLMST の Algebra）、接頭辞 `prop247_`・`paper*`、
  ファイル名の Prop247・Cor404 など、CLMST の `Inputs/`（中身はすべて証明済み）。内容の名前を付ける。
  例外：Paper/ のディレクトリ名 Section2〜Section5 は論文の節に合わせて残す（ファイル名は内容の名前、論文の番号は docstring に）。
- 裸の `SerrePositivity` 名前空間や、ファイル名から付けた名前空間に一般的な名前（`section_sum0`・`familyMap`・`map`・`identity` など）を置かない。
- `def …Law : Prop` で等式を包まない。補題の主張に直接書く。
- `backward.isDefEq.respectTransparency false`・`backward.defeqAttrib.useBackward true` などの移行用オプションは、統合のときに外せるか試し、
  外せなければ `section` の範囲に限る。`maxHeartbeats` の引き上げも同様。
- docstring は日本語の 概要／方針／規約／使われ方 にそろえる（英語のもの、定型文の繰り返し、古い状況の記述を直す）。

予約したディレクトリ名（2026-11-02 ユーザー、同日に 2 つ追加）：区切り 2b の後に BS の一般論を受け入れる下位ディレクトリ。いずれも第一層（一般論）として扱う。
`HomologicalAlgebra/Cosimplicial/`（余単体加群・余単体可換環の全複体の積など）、`CommutativeAlgebra/DeRham/`（多項式環の de Rham 複体と p 進完備化）、
`CommutativeAlgebra/UniversalHomeomorphism/`、`CommutativeAlgebra/EtaleStratification/`。論文の層の作業ではこの 4 つの名前を別の用途に使わない（中身はまだ置かない）。

## D. 章をまたぐ共通の仕組み

一つの章だけで作業すると重複が残るものを、担当の章と一緒に挙げる。

1. **Euler 標数・K₀**：CT の HomologicalEuler・ExactSequenceEuler・TriangulatedK0、KTheory の SupportedExactEuler と G₀、PC の `chiOrd`・`chiLam`・
   `lambdaEuler`・`integerEuler`、LA の `perfectEuler`・`koszulEuler`、IM の `chi`、CA の `homologyLengthSum`、Asymptotic の `*EulerK0`（5 系統）。
   担当は CT（§1.2）：`homologicalEulerK0` の値域を任意の `AddCommGroup`、定義域を `IsSerreClass` な部分圏上の関数に一般化する。他の章はその上に
   乗る（§6.2.3・§4.2.3・§7.5）。種類どうしの比較の補題は LA の比較ファイル 1 本に集める（§5.7）。`chiOrd_eq_alternating_term_lengths`
   （CA/Length/Euler）と `chiOrd_eq_of_quasiIso`（B2 で PerfectComplex 群へ回した）も同じ場所へ。
2. **有限位数の作用・テンソル冪・冪等元**：HA の CochainTensor・CochainIdempotent、PC2・PC3、KT2・KT3、CT の TriangleIdempotent・CubicConjugation。
   共通の設計は `CochainCyclicAction n`・`weightedK0Class`・環の層の固有射影（§4.4.5・§6.5）。テンソル積の本体は `HomologicalAlgebra/CochainTensor/`
   に置き、Mathlib のモノイダル構造の記法へ寄せる（§3.8・§4.3.2）。
3. **純な対象と `singleFunctor` の標準同型**：HA の `normalizedPureHomologyIso`（§3.3.5）と CT の `derivedPureHomologyIso`（§1.2.3）はどちらも
   `.choose`・`Classical.choice` で作られた同じもの。CT に 1 本、明示的な構成で（BS が名前を使うので名前は残す）。
4. **Koszul の住み分け**：定義と分解であること → CA/Koszul（`Koszul.lean`・`KoszulResolution.lean` は BS のため凍結、E の作業時間に `Koszul/` へ）。
   ホモロジー代数（Tor・Ext・局所コホモロジー・係数関手） → HA。長さ・Euler 標数 → LA（λ）と PC（K₀）。導来完備化の塔 → HA/DerivedCompletion。
   Asymptotic の KoszulBaseChange（§7.2）と CLMST の `parameter_power_isKoszulResolution`（§8.2.1）は CA へ。
5. **almost 数学**：一般論 → CA/Almost、長さ → LA/Almost、perfectoid イデアル → BS/Almost（§5.7・§8.2）。
6. **根の塔**：CA/RootTower（CLMST の Stage* を RootTower/BaseChange に、LA の StageDecay も）、長さ → LA/RootTowerLength、perfectoid 化
   （MixedPerfectoid）→ BS（§8.2）。
7. **台**：本体は `HasHomologySupportOn`（§4.2.3）。加群の台の補題は CA（ModuleSupport・SupportDimension）へ集める（KT の台の補題 §6.2.5、
   CT の ScalarSupport §1.2.1）。SupportHeight・ModuleSupportHeight・SemilocalSupport は KT1 の G0/SemilocalSupport へ（§6.2.1）。
8. **`IsModuleSTorsion` の廃止**（`Module.IsTorsion'` へ、§2.6 の決定）は KTheory の KT1 の 5 ファイルに波及する。E を先に行い、KT1 はその上で。
9. **削除の前に章をまたいで確かめるもの**：AsymptoticLengthBounds・ResolutionFamilies は Asymptotic へ移す（§4.2.1）。EulerLimit の補助
   （§7.2）は PC ではなく Asymptotic/NormalizedLimit へ。

## E. 段階と順序

**段階 0：殻と死んだファイルの一掃**（BS の再ビルドはほぼ起きない。CLMST の分は段階 2 へ）
- 区切り 0：再エクスポートだけのファイル 49 本（機械的に検出：PC 33・KT 9・HA 3・CA 1（PerfectTorIndependence）・LA 1・CT 1（EulerTheory）・
  Paper/Section4/Foundations）と死んだファイル 24 本（HA 7・KT 5・LA 8・Asymptotic 4）を削除し、利用者の import を殻の中身へ展開して張り替える。
  dévissage の不要な import を外す（G の 5）、`PerfectComplex/K0.lean` の docstring（G の 6）。Asymptotic/PaperVanishing は Paper/Section4/FlatRealization が
  使うので残した（§9.5）。∞ 基盤へ渡したもの（CT の下位ディレクトリ・Nerve・殻 11 本・∞ 側だけが使う 12 本・ArrowFactorization*、HA/ComplexLimits、EInfinity の殻、GroupTheory/Coxeter、Inputs/Homotopy）は対象外。
- 区切り 0 の追加分：Inputs の殻 3 本（RegularLocalRing・RegularParameters・Unmixedness、§11.1）、Paper の再エクスポート 3 本（Section2/Tower・
  MonomialBasis・TowerStage、§10.3）、古い正値性の経路 2 本（Section5/AsymptoticPositivity・SecondComparisonLowerBound、G の 8）。
- 確度高の Mathlib への置き換え（各章の「Mathlib との重なり」の確度高のもの、30 件程度）は独立の区切りにせず、各区切りで該当する群を統合するときに一緒に行う（2026-10-30）。

**段階 1：BS に触れない統合（下の層から、区切りは 4 つ）**
区切りの中は群ごとに「新しいファイルと直接の利用先だけのビルド」で進め、全依存ビルドは区切りの最後に 1 回だけ流す（2026-10-30）。
見込みは区切り 1-1 が約 250 本、1-3 が約 200 本（B1+B2 の約 3 倍）。
- 区切り 1-1：CT のトップ階層（§1.2。Euler・K₀ の一般化と純な対象の同型は除く）と CA の残り（E §2.6、D・H・X のうち BS に依存しないもの
  §2.7〜§2.9）、Paper の一般の補題のうち CA へ行くもの（§9.2）。
- 区切り 1-2：HA の第一層（§3.7）。
- 区切り 1-3：D の 1（Euler・K₀ の一般 API、§1.2）と D の 3（純な対象の同型）、LA の核・PC・IM の層の整理（§5.2・§4.5）、PC（§4）・LA と IM（§5）の
  統合、Paper の一般の補題のうち LA へ行くもの（§9.2）。
- 区切り 1-4：KTheory（§6）と Asymptotic（§7）、Paper の再構成（第 10 章）。
CT の下位ディレクトリ（§1.3）・Nerve まわり・HA/ComplexLimits は ∞ 基盤の指示書で行う（伝達済み、handover-ct-to-infinity-2026-10-30.md）。

**段階 2：BS の作業時間（2 回）**
BS の作業の区切りに時間を決め、BS 側の編集を止めて行う。それぞれ全依存ビルド 1 回でコミットする（BS/CLMST の分は独立コミット）。準備（スクリプト）は
段階 1 の間に済ませる。
- 区切り 2a（BS の層の境界）：CA の H 群の BS 依存部分を BhattScholze/ へ（§2.8）、CLMST の基礎と論文の分離（§8）、`Koszul.lean`・`KoszulResolution.lean` の
  `Koszul/` への移動、IteratedTensor* の BhattScholze/Prism/Tensor/ への移動（§3.8）、段階 0 で残した CLMST の死んだファイル。
- 区切り 2b（HA の DerivedCompletion）：HA の第二層（DerivedCompletion の BS 向けファイル、Pair の置き換え、PD の d = 0 の整理、導来テンソルの一本化、§3.7）。
  中身の書き換えが大きいので、先に worktree で準備し、作業時間には取り込みと全依存ビルドだけを行う。

**段階 3：大きな一般化**（段階 1・2 の後に費用対効果を見て判断）。B4（Pair の Principal の反復への置き換え）は完了（2026-11-04）。下の残り 3 項目は段階 II の計画（[stage-ii-plan-draft.md](stage-ii-plan-draft.md)）の保守と K 理論の節で扱う（2026-11-05）
有限位数の作用とテンソル冪（§6.5・§4.4.5、HA の CochainTensor の Mathlib 化）、Asymptotic の商の二本立ての一本化（§7.5）、PC の K₀ のモデルの
一本化（§4.2.3）。

**Mathlib を上げる時期**：**この整理の間は上げない**（2026-10-30 決定。BS など他の作業と干渉するため）。固定版（`lake-manifest.json` の rev、
2026-10-07）のまま全段階を終える。ただし作業の途中で、最新版（`/tmp/mathlib-latest`）に上げると直す必要がある箇所（改名・非推奨・
最新版にしかない置き換え先）に気づいたら、H の表に記録しておく。

## F. 状態

| 範囲 | 状態 |
| --- | --- |
| **全体** | **区切りはすべて完了**（2026-11-04：2a 590c4eff7・2b 08a2997fd・段階 3 の B4 3de4d3ba9 を main に取り込み済み）。段階 3 の残り（有限位数の作用とテンソル冪・Asymptotic の商の二本立ての一本化・PC の K₀ のモデルの一本化）は段階 II の計画（[stage-ii-plan-draft.md](stage-ii-plan-draft.md)）の保守と K 理論の節へ移した。このレーンは閉じた（2026-11-05） |
| LinearAlgebra・FieldTheory・RingTheory | 見直し完了（2026-10-29） |
| CommutativeAlgebra の G・A・F・C1〜C3・B1・B2 | 完了（§2.1） |
| 段階 0 の区切り 0 | 完了（65f178a5b・7820689c7、追加分 8 本も完了） |
| 区切り 1-1（CT トップ階層・CA の E・D・X・H の BS に依存しない部分・Inputs の包み・Paper の一般論の一部） | 完了（2026-10-30、記録は下の表と「区切り 1-1 で見送った項目」） |
| CommutativeAlgebra の H の BS に依存する部分（P1 普遍性・P8 perfectoid イデアル）・RootTower/Koszul | 完了（区切り 2a） |
| 区切り 1-2（HomologicalAlgebra の第一層、§3.7） | 完了（2026-10-31、記録は下の表と「区切り 1-2 で見送った項目」） |
| 区切り 1-3（LA・IM・PC・HA/CochainTensor の統合、D の 1） | 完了（2026-10-31、記録は下の表と「区切り 1-3 で見送った項目」） |
| 区切り 1-4（KTheory・Asymptotic・Paper の統合、DG の依頼の Perfect、§10.4 の重複） | 完了（2026-11-02、refactor/1-4 で verify PASS。記録は下の表と「区切り 1-4 の記録」） |
| 区切り 2a（BS の層の境界：CA の BS 依存・CLMST の基礎と論文の分離・Koszul・IteratedTensor） | 完了（2026-11-04、verify PASS gate:true 99/99、main 590c4eff7。記録は下の「区切り 2a の記録」） |
| 区切り 2b（HA の DerivedCompletion の第二層） | 完了（2026-11-04、A・B1〜B3・B4a、verify PASS gate:true 99/99、main 08a2997fd。B4 の本体は段階 3 として 2026-11-04 に完了、main 3de4d3ba9。記録は下の「区切り 2b の記録」） |
| HomologicalAlgebra・PerfectComplex・KTheory・CategoryTheory（トップ階層）・LengthAlgebra・IntersectionMultiplicity・Asymptotic・CLMST・Paper | 区切り 1-2〜2b で完了。残る大きな一般化は段階 II へ |
| CategoryTheory の下位ディレクトリ・Nerve・HA/ComplexLimits | ∞ 基盤の側へ移管（R75〜R78、伝達文） |

区切りごとの記録（ファイル数・行数の前後）：

| 区切り | コミット | ファイル数 | 行数 |
| --- | --- | --- | --- |
| B1+B2（参考） | 7242dc7f7・e0308bb75 | CA で約 70 本を約 30 本に | — |
| 区切り 0 | 65f178a5b・7820689c7 | 73 本を削除（shared の対象 1407 → 1367 モジュール） | −2434・＋295（import の展開） |
| 区切り 1-1 | ca2fffe4d・25d50e9e8 | 203 本を削除・55 本を新設（CT 68 → 20、CA の E・D・X・H 約 120 → 約 35、Inputs 6 本を削除、shared の対象 → 1156 モジュール） | −19100・＋17583 |
| 区切り 1-2 | 95c0a6d25・401fbbe6d | 153 本を削除・24 本を新設（HA1 69 → 13、HA3 31 → 5、HA4 33 → 5、HA5 20 → 2、shared の対象 → 1058 モジュール）。未使用の宣言 189 を削除 | −16182・＋13361 |
| 区切り 1-3 | e032f83ea・ea54f9f4c | 166 本を削除・40 本を新設（LA・IM・CA/Almost 74 → 22、PC と HA/CochainTensor 100 → 26）。未使用の宣言 62 を削除 | −19012・＋17681 |
| 区切り 1-4 | 3b825cacb・bbba9ee39（refactor/1-4、main 5c909058e を取り込み） | 247 本を削除・32 本を新設（ほか改名 18）。KTheory 127 → 28、Asymptotic 81 → 15、Paper 61 → 20、Devissage 7 本は research へ。未使用の宣言 48 を削除。shared の対象 752 モジュール | −25174・＋23077 |


区切り 1-1 で見送った項目（2026-10-30）：

- 他の区切りへ：Almost（CA/Almost と LengthAlgebra/Almost* を一つの群として 1-3）。SubmoduleExact（1-4、KTheory）。MinimalGenerators・PerfectTorIndependence/Basic（1-2、HA）。
  Lemma3_5 の `radical_span_eq_maximalIdeal`・`isKoszulResolution_of_regular` と GaloisNormalization の private `powerSeriesMapEquiv`・`wittMapEquiv`
  （節の変数に依存するので Paper の再編 1-4 で）。H の P1（IntegralPerfectoid・Perfectoidization*）・P8・Perfectoidization の Inputs（2a）。
- 移し先を保留：ConductorQuotient（利用者が PerfectComplex/QuotientLength なので Paper へ移すと層が逆転する）、AlgebraMapCokernel、LocalResidueLinearMap、
  PrincipalMaximalFactorization、FrobeniusHypersurfaceGrowth・FrobeniusKoszulLimit。
- Mathlib への置き換えを見送ったもの：`perfectClosure_lift_of`（Mathlib に対応する補題がない）、`principalAnnihilator`（所属の補題 a·z = 0 の形を多く使う）。
  `tiltRootEvaluation`（MonoidHom として使う）。
- 未使用だが残したもの（BS への供給）：Fontaine 核の分離性の連鎖（`IsIntegralPerfectoid.fontaine_kernel_isHausdorff` ほか 10 宣言、Perfectoid/Fontaine）。
  BS の `wittRegularQuotientFontaineMap_surjective`・`_bijective` の仮定 `IsHausdorff (ker θ)` を満たす唯一の証明で、audit_f7 が確認する
  （2026-10-30 ユーザー、一度削除して戻した）。`perfection_principal_quotient_zero_branch` は削除した（audit_f6 の該当定理も）。
- 未使用だが残したもの：Support/Closed の `supportPullback` の関手性（id・comp・mono）、PerfectRing の `radicalIdeal_idempotent_*`（提出候補）、
  PerfectPolynomial の `perfectPolynomialHomEquiv`・`perfectPolynomial_hom_ext`、`compatibleRootsTilt_coeff`（simp 補題）。
- 未決：E の共通モデルの重複の共通化と一様な冪の補題の一本化をどの区切りで行うか。
- 計画からの変更：ModuleSupport も Support/Closed に入れた（ModuleClosedSupport との import の循環を避けるため）。冪ねじれ 5 本は D の既存ファイルではなく
  新しい PowerTorsion/{Basic, Category} にまとめた。Paper の PerfectApproximation は CA/Perfection/Approximation へ、核の長さの評価だけ Paper に残した。

他のレーンからの申し送り（2026-10-31）：DG-W1 が main に入るとき、ルートの DG の import 12 行を `SerrePositivity.DifferentialGraded` 1 行に置き換え、
DifferentialGraded/Complexes/Monoidal と Stage* を削除する。DG-W2（D3）で DifferentialGraded/Verdier/OrderSquare とその検査 2 本を
Asymptotic/DGVerdier/ へ上げる。区切り 1-4 の Asymptotic の統合には Asymptotic/DGVerdier/ も含める（2026-10-31 DG 側の希望）。ただし DifferentialGraded に依存するので、論文の層の Asymptotic のファイルには混ぜず、別の小群として整理する。ルートの `SerrePositivity.lean` は
区切りの作業でも書き換えるので、DG の取り込みは区切りのコミットの後に合わせる。

∞ の束（W1+W2a、R79 を含む）との調整（2026-10-31）：DG-W1 は区切り 1-3 の後に main へ入った（194a65110）。束の適用から verify が通るまで
（10-31 21:30 開始、11-01 の昼ごろまでの見込み。この間は main でのビルドも控える）、HomologicalAlgebra・CategoryTheory・HomotopicalAlgebra・InfinityCategories・KST・EInfinity・
ルート・それらの監査に触れる取り込みを止める。CommutativeAlgebra・Paper・Asymptotic・BS 側は構わない。束が終わったらハッシュが届くので、
順序は 束 → DG-W2(b)（Asymptotic/DGVerdier/ の新設を含む、約 4 時間）→ 区切り 1-4 の取り込み。束の後に formalization-plans/k-theory.md と formalization-plans/k-theory-generalization-inventory.md を削除し、formalization-plans/README.md の「案内」の表の
HA と CT の 2 行を更新する（DG の 2 行は DG 計画の D5 で）。main のビルドは他のレーンと並行させない。

DG レーンからの依頼（2026-10-31）：DifferentialGraded/Perfect/ が PerfectComplex の `strictlyPerfectComplex`・`PerfectHomotopy`
（Perfect/HomotopyCategory）、`strictlyPerfectComplex_biprod`（BiproductPerfect）、`finiteProjective_exists_retract`（KoszulLength）に依存している。
前の 3 つは HomologicalAlgebra の軽いファイルへ下ろし（名前は残す）、`finiteProjective_exists_retract` は Mathlib の
`Module.Finite.exists_comp_eq_id_of_projective` に置き換える。DG → PerfectComplex の辺が消える。HA は ∞ の束の間凍結されるので、
凍結の明けた後、区切り 1-4 で行い、モジュールの対応表を DG 側へ伝える（それまで DG 側は例外として登録）。

区切り 1-2 で見送った項目（2026-10-31）：

- BS が直接 import するので動かさなかったもの（第二層へ）：KProjectiveLift・BoundedAboveDerivedAssociator・BoundedAboveDerivedBaseChange・
  SequentialComplexColimits・MilnorAnnihilator。ProjectiveBaseChange と SequentialChainHomologyColimits の削除も、使う側が BS の import する
  ファイルなので第二層へ。KProjective の持ち上げ 3 本の一本化（KProjectiveLift が BS の import 先）も第二層へ。
- import の循環を避けるため単独のまま残したもの：BoundedAboveDerivedUnit（Associator を挟む）、KoszulDualBaseChange（Ext/LocalCohomology が import する）、
  TowerProjection（KoszulTower・TowerUnit の上にある）。TowerUnit は一般部分と Koszul 部分に分ける必要があるので未着手。
- HA1 の Tensor/*（決定 3 により PC2 と同時、区切り 1-3）。CochainTensor* の未使用 7 件もそこで扱う。
- HA2・HA3 の Tor 側・HA5 の BS 向けの群の統合は第二層。
- Mathlib への置き換えを見送ったもの：`free_baseChange`・`finite_baseChange`（呼ぶ側で `extendScalars` の対象をテンソル積に直す `change` が要り、
  1 行のインライン化にならない）。確度中の置き換え（`isZero_homology_of_isZero_X` など）は未着手。
- 監査スクリプトが名前で参照しているため残した未使用の宣言 15 件（KoszulMilnor・ModuleTower・PairKoszulProduct など）。
- 計画からの変更：Auslander–Buchsbaum は削除しない（§3.8 の 1 の訂正）。HA1 の MonoidalUnitHomRing・MonoidalPointAction は CategoryTheory/MonoidalUnitHom に。

区切り 1-3 で見送った項目・注意（2026-10-31）：

- D の 1 は値域の一般化だけ行った（`homologicalEuler`・`homologicalEulerK0` と長完全列の加法性は任意の加法群に値を取る。ℝ で項を比べる 5 本に
  `zsmul_eq_mul` を足した）。評価の定義域を `IsSerreClass` な部分圏にする一般化は区切り 1-4（G₀）へ。
- D の 3（純な対象の同型の一本化）は区切り 2a へ（`normalizedPureHomologyIso` が BS の import する HA/DerivedPureHomology にある）。
- Paper の一般の補題のうち LA へ行くもの（§9.2 の PerfectApproximationLength・TowerApproximation）は区切り 1-4 へ（TowerLength・TowerDescent を
  先に移す必要があり、第 10 章の再構成と一体）。
- §5.2 の 2（ResolutionEvaluation の前半を PC へ）・3（`chi` を HA の Tor の近くへ）・4、§5.3 の名前空間のそろえ・StageDecay の移動は未着手。
- PC から KTheory・Asymptotic へ移すもの（IntegerEuler 系・Adams の Koszul・FiniteProjectiveResolutions・AsymptoticLengthBounds・
  ResolutionFamilies・TensorTorComparison・TensorResolutionLength・RankOneTensorTripleExt）は区切り 1-4 へ。PC の一本化（K₀ のモデル・台の条件・
  閉包補題）と CochainTensor の Mathlib の記法への寄せは未着手。
- 監査が名前で参照するため残した未使用の宣言 11 件。
- 統合で import の範囲が広がった影響：CochainTensorBounds の `Mathlib.Algebra.Homology.Embedding.CochainComplex` を CochainTensor/Basic に入れると、
  Basic だけを使うファイルで `K.ιTruncLE` などのドット記法が Mathlib の `CochainComplex.ιTruncLE`（ℤ を取る版）に解決されるようになり、KST・∞ 側で
  エラーになった。Bounds と Finite を CochainTensor/Bounds に分けて解消。HA/ModuleTensorCochainExact の `tensorRight` の `Epi` の探索は重くなったので
  その補題だけ `synthInstance.maxHeartbeats 80000` にした。重い import を軽いファイルへ統合しないことを今後の統合の注意とする。

区切り 1-4 の記録（2026-11-02、worktree refactor/1-4、main 8a6f1d918 から。main 5c909058e を取り込んだ後に verify PASS：bbba9ee39、ビルド 2・監査 100・sorry 閉包 1 がすべて成功、gate true、80 分 38 秒）：

- 1 回目の verify はルートのビルドで TensorCubeLowMixed が失敗した（未使用の宣言を消したとき、直前の `set_option … in` 2 行が残った）。直して再実行。
- ファイル（main 8a6f1d918 との差、名前の付け替えを含む数え方）：264 本を削除・49 本を新設（KTheory 127 → 28、CA の SupportHeight・SemilocalSupport・ModuleSupportHeight・SubmoduleExact を吸収。
  Asymptotic 81 → 15（うち Paper/Section4/{RankQuotient, RankLowerBound} の 2 本）。Paper 61 → 20、うち LA/RootTowerLength/{Tower, BaseChangeApproximation}
  の 2 本）。Devissage* 7 本は research/kt-devissage/ へ（11-01 決定）。行数は −25174・＋23636（research を除く）。
- 計画からの変更：
  - Asymptotic/PaperRankQuotient は Asymptotic/Completed に置いた（DGVerdier/OrderSquare が import するので Paper へ移すと層が逆転する）。
    DGVerdier の 3 本はそのまま、OrderSquare の import だけ `Asymptotic.Completed` に。
  - PaperVanishing は死んでいなかった（変種の FlatRealization が使う）。Paper/Section4/RankLowerBound の一部にした。
  - KoszulBaseChange の `baseChangeKoszulOnIso` は CA/Koszul へ（名前空間は `SerrePositivity.Asymptotic` から `SerrePositivity` に。利用者は
    `SerrePositivity.Asymptotic` の中なので書き換え不要）。
  - LengthAlgebraConsequences は Section2/LengthAlgebra に入れず、軽い Paper/Section2/LengthAlgebra/Formulas に分けた。Section2/LengthAlgebra
    （Theorem 2.5、BS・CLMST に届く）と同じファイルにすると、それを import する Section5/Positivity の ApproximationPositivity の `variable` で
    instance 探索が時間切れになった（1-3 の「重い import を軽いファイルへ統合しない」と同じ現象）。
  - Section2/BaseChange は作らなかった。§10.4 の一本化により Cor 2.6 の 1・2 は Section3/LengthComputation に置いた（下）。
- §10.4 の重複（決定 3）：Cor 2.6(3) は主経路の `Section4.residue_length_pos_of_lengthAlgebra_values`（Section4/LengthHypotheses、docstring に論文の番号）
  を残し、`Section2.cor_2_6_residue_pos`（Section2/Corollary2_6、ファイルごと）と包みの `cor_2_6_pos` を削除。Cor 2.6(1,2) の `cor_2_6_tor` は
  `lemma_3_4` を `T = D` で適用する 2 行の証明に（同じ議論の二重を解消、`lengthAlgebra_base_values_one` は不要になり削除）。(2.5) の v = 1 は
  `parameterQuotient_length_eq_multiplicity`（Positivity、一乗の値の書き換えだけ）と Formulas の `parameter_quotient_values_pow` が残る（計算の重複ではない）。
  Thm 4.7・FlatRealization の並行と正値性の二経路は変種として残す（G の 8）。
- DG の依頼：`strictlyPerfectComplex`・`perfectHomotopyProperty`（と `_quotient`・`_zero`・`_shift`・`_mappingCone`・三角部分圏の instance）・
  `PerfectHomotopy`・`perfectHomotopyInclusion`・`perfectHomotopyObj`・`cochainBiprodXIsoProd`・`strictlyPerfectComplex_biprod` を
  新しい HomologicalAlgebra/Complex/StrictlyPerfect へ（名前は変えない）。PC/Perfect/HomotopyCategory と PC/BiproductPerfect はそれを import する。
  DG/Perfect/Basic は `finiteProjective_exists_retract` を Mathlib の `Module.Finite.exists_comp_eq_id_of_projective` に置き換え、PC/KoszulLength の
  import を外した。DG/Perfect/Ring/FiniteProjectiveComparison は PC の 2 本の代わりに HA の 1 本を import する。DG → PC の辺は無くなった
  （scripts/refactor/layers.json の例外 3 件は DG-W3 で外す）。
- docstring：15 群（Asymptotic・Paper/Section4）と 19 群（Paper・LA/RootTowerLength）を規約の形で新しく書いた。LengthAlgebraConstruction・Theorem 2.5 の
  「Roberts の引用に依存」を直した（等標数は FrobeniusGrowth の初等的な評価を使い、Roberts の一般定理には依存しない）。旧ファイル名の参照 25 か所を
  新しいパスへ。Section3/NormComparison の旧ファイルの閉じ `end` 2 か所を除いた。
- 未使用の宣言（2026-11-02 ユーザーの方針：論文の主張は残す、一般論として意義のあるものは残す、それ以外は消す）：scripts も参照元に数えた走査で
  scripts・文書の参照がない 80 件のうち 41 件を残し（論文の主張と変種 13・一般の補題 28）、40 件を削除した。KTheory/Adams の計算の足場 28
  （KoszulCube の次数ごとの同型 9・KoszulCubeFourier の基底の同型 3・KoszulSquareSplitting の双対の等式 3・TensorCube の First layer 2・Low/High mixed の
  回転と余核の同型 6・TensorSquare の対角と四項の同型 6）、`heightStratumComplement_le_primeCompl`、PaperVanishing の `_vanishing_of_koszul`・
  `Betti_eq_zero_of_isZero`、旧 ApproximationEuler・ApproximationBetti の正値性の旧経路の中間段 8（`paperOrdinaryEulerK0_eq_twistedEuler` ほか。
  走査が見落とした利用者 `exists_supported_approximation_with_lambdaChi` も未使用なので合わせて削除し、ApproximationEuler のパートは空になったので除いた）。
  exposition/ja/exposition-ja.tex の 1070 行が `paperOrdinaryEulerK0_eq_lambdaChi` と旧モジュール名を参照している（exposition の側で直す）。
- 見送った項目：
  - 名前空間の `SerrePositivity.Paper` へのそろえ（決定 1）。
  - 文書（.md・.py）だけが名前を挙げる未使用の宣言 86 件は、同じ方針で 78 件を残し、8 件（KoszulSquare の次数ごとの同型 7・
    `tensorCubeHighMixedCokernel`）を削除した（2026-11-02 ユーザー了承）。
  - KTheory の Mathlib への置き換え（§6.2.2：Coefficient*・`g0CoefficientMap`）、PC から KTheory・Asymptotic への移動、Euler の定義域の一般化
    （IsSerreClass）、Paper → LA の一般の補題（§10.6）の残り、§5.2 の 2〜4、StageDecay、Lemma3_5・GaloisNormalization の補助。
  - maxHeartbeats：統合で各パートを `section … end` で包んだので、ファイル全体の `set_option` はパートの範囲に限られた。個々の引き上げの値は変えていない。
  - scripts/check_adams_import_boundaries.py は 1-3 の HA の統合の時点で古い名前を参照している（verify からは呼ばれない）。直すか削除するかは後で。

区切り 2a の記録（2026-11-02、worktree refactor/2a、main d27c4798d から。全ビルドの前）：

- 層の境界：CA・HA・LA から BS・CLMST への import は 0 件になった。BS → CLMST（BS/Almost/PerfectoidAlmost → CLMST.Almost）と
  Paper → CLMST の再エクスポート（Paper/Section2/MixedPerfectoid、削除）の逆転（§8.5）も解消した。KST → BS は MonicRelation の 1 件が残る（下）。
- CA の BS 依存の 12 本 → BhattScholze の下の 6 本：`PerfectoidIdeal/{Basic, Powers, Cover}`・`Perfectoidization/Finite`・
  `Semiperfectoid/AbsolutelyIntegrallyClosedQuotient`・`Andre/OrdinaryRoots/MonicRelation`（宣言名は変えない）。
- CLMST の基礎（A）：
  - BS に依存しないもの 20 本 → `CommutativeAlgebra/RankLocus`・`HomologicalAlgebra/FiniteFreeComparison`・`CommutativeAlgebra/ModPHypersurfaceGrowth`・
    `CommutativeAlgebra/RootTower/StageModPLength`・`HomologicalAlgebra/DerivedCompleteCommonModel` と既存 3 本への追記。Stage* の 10 本 →
    `CommutativeAlgebra/RootTower/BaseChange`（名前空間 `Section2`。`RPerfd` への写像は CLMST に残す）。
  - BS に依存するもの → BhattScholze の下の 12 本（`Andre/TorDescent`・`PerfectoidIdeal/{Roots, Tor, CompletedQuotient, TorCriteria}`・
    `Perfectoidization/{Cone, ExcisionComparison, ExcisionTor, CompletedTensorComparison, FiniteComparisonExcision, RootTower}`・
    `Semiperfectoid/{Product, QuotientPerfectoidization}`）と BS/Almost/PerfectoidAlmost への追記。
- CLMST の論文側（B）：77 → 18 本（承認済みの名前：`PerfectoidizationIsogeny/`（12 本）・`AllModuleTorVanishing`・`KoszulAnnihilation`・
  `CyclicLengthBound`・`ParameterQuotientLength`・`ParameterPowerLength`・`Algebra`）。CLMST/Inputs/ は吸収した。CLMST は 146 → 18 本。
- 削除：§8.4 の死んだ 11 本、主経路外のうち 3 本（TensorOrder の残り・CompletedCokernelKoszul・Inputs/AlmostLength、11-02 決定。残りの 5 本は
  BS・CA へ移して残した）、`finiteAlgebraConeIsogeny`。
- 重複の一本化：mod pᴺ の冪等性（3 → BS の 1）、`perfectoidIdeal_quotient_isIntegralPerfectoid`（2 → BS の 1）、`corollary_4_0_4`（2 → 1）、
  有限比較 excision の証明（Prop247Proof の別証明 → `BhattScholze.klFiniteComparisonExcision_of_perfectoid`）、`Inputs.proposition_2_4_7` の入口。
  CLMST の `completedTowerRoot*` の別名 5 つを削除（`Section2` の本体を使う）。
- 改名：`prop247_` を 74 個の論文側と、基礎の 40 個余りから外した。宣言の改名表は計 296 件（scratch の rename_all.json、2a の取り込み時に BS へ回す）。
- その他：Koszul・KoszulResolution → `CommutativeAlgebra/Koszul/{Basic, Resolution}`。IteratedTensor の 6 本 → `BhattScholze/Prism/Tensor/IteratedTensor`。
  P1：Perfectoidization* → `CommutativeAlgebra/Perfectoid/{Defs, Completion}`（Nilpotent は Torsion へ、未使用だが一般論なので残す）。
  PerfectoidDerivedComplete → `HomologicalAlgebra/DerivedCompletion/IntegralPerfectoid`。`IsPerfectoidization.comp_ringEquiv` → CA の Perfectoid/Defs。
- ファイル：main d27c4798d との差で 160 本を削除・33 本を新設（改名 15）、−13933・＋12862 行（SerrePositivity のみ）。
- 見送り・未決：
  - MonicRelationRegularSequence は BS のまま（KST → BS が残る）。BS の Andre/OrdinaryRoots の多項式の補題を CA へ下ろす件は未決（11-02）。
  - Inputs/Perfectoidization は BS の管轄のまま（BS セッションと調整）。
  - 2b へ：Prop247ConeComparison・Prop247Cone・Prop247RankCompleteness の一般部分（HA/DerivedCompletion へ）。
  - `hetale` の長い仮定を名前つきの述語にする件、Corollary404 などの不要な import（§8.4）は未着手。
  - CA → HA の import は 2a の前から 40 か所以上ある（層の規則の対象外）。
- 全ビルドと verify（11-03 夜〜11-04、main 3e27dda00 を取り込んだ f4e4c1724 の上）：監査を make_area_audits で再生成（a85cfff19。
  bhatt_scholze は 2a で BS の下へ移したファイルを含めるため再生成版を残した）。1 回目（VERIFY_JOBS=3、65 分）は audit_clmst の 1 件で FAIL：
  RootTower/BaseChange へ移した `stageAlgebraIsNoetherianOfBase` の名前空間が `Section2` に変わっていた。f3daa70ad で直し、2 回目
  （VERIFY_JOBS=6 VERIFY_MEMORY_GB=40、24 分）は **PASS gate:true、監査 99/99、sorry 閉包 PASS**。改名表は名前空間の突き合わせで 16 件
  （上の 1 件と、29b688d02 でファイルごと消した Prop247 の宣言 15 件の「削除」）を足して 312 件。

区切り 2b の記録（2026-11-02 夜、worktree refactor/2b。A のみ、未ビルド）：

- 条件（ユーザー、coordination.md 207343063）：B は (i) DerivedCompletion の外から使われる宣言の型を変えない（snapshot の型ハッシュで確認、def の
  本体は可）、(ii) BS・CLMST の証明は編集しない、(iii) 11-05 までに終わらない項目は段階 3 へ、(iv) 小さなビルドは coordination.md §2-4a。
- A：HomologicalAlgebra/DerivedCompletion を 135 → 44 本（§3.5・§3.6 の表の 28 群）。表どおりに組むと import が循環する箇所は群を分けた
  （Koszul/{Tower, Complete, Milnor}、ModuleComplete/{Basic, Closure, Presentation}、ComplexCompletion/{Basic, Reconstruction}、Principal の Classical、
  CompletionReflection から KProjectiveProduct）。ModuleResolution・PairZeroCompletion・RegularCompletionPure・KProjectiveProduct・PrincipalClassicalComparison は
  単独のまま（循環を避けるため）。宣言名は変えない。BS・CLMST は import 行だけ。
- 2a から回した CLMST の一般部分：Prop247Cone・Prop247RankCompleteness の一般の 6 定理 → DerivedCompletion/IntegralPerfectoid（内容の名前に改名）、
  Prop247ConeComparison の 4 宣言 → DerivedCompletion/CompletedTensorVanishing（名前空間 `DerivedCompletion`）。
- 計画で削除とされていた ModuleConeCoordinates・ModuleConeNaturality・AdicTower・CompletedTensorModuleReduction・FlatResidueLimitTorsion・
  PowerTorsionTorProduct は既にない。
- BS の依頼（CompletedTensor の分割、仕様書 completed-tensor-split.md）は 2a に入れない。2a の取り込みの後に BS が BS-W10 の作業 A として行い、
  2b の全ビルドに相乗りする（11-03 ユーザー決定）。**2b の全ビルドの前に main を取り込み、BS の変更を含める**。CLMST の 5 本の import 行は BS が直す。
- 2a の小さなビルド（98484d01e、274 本）の失敗 3 件を修正（aae233fb5 ほか）：新しく書いたファイルの `noncomputable` の抜け 2 件と、BS の名前空間へ
  移したファイルで BS の別名（`alias compatibleRootFamilyIdeal := …`）に修飾なしの名前が当たった 1 件。失敗した 3 本の下流は未検証。
- A の小さなビルド（183 本）は通過（11-03）。
- B（11-03、項目ごとに別コミット。どれも 107 本の小さなビルドが通り、snapshot（.lake/verify/2b-before.json との比較）で外から使われうる宣言
  715 本の型の変化 0・消えた宣言 0）：
  - B1（ebe3bec91）：`.choose` の def 化。`principalCompletionLift(AlgHom)`・`pairCompletionLiftAlgHom` を加え、Principal/Comparisons・
    PairZeroCompletion・PrincipalClassicalComparison・CompletedAlgebraH0 の `.choose` を置き換えた。Reflection は `Function.surjInv`。
  - B2（663126e92）：「完備化は、完備性を保つ関手と可換」を `completionCommComparison`（`_unit`・`_naturality`）1 本にし、ScalarCone と
    QuotientBaseChange の比較はその例にした。
  - B3（c85ae14cf）：PD の d = 0 の層をなくした。`completedTensorH0PrincipalRingEquiv` は H⁰ で可逆な完備化した添加と
    `completedAlgebraH0NatPrincipalAlgEquiv` の合成、`completedTensorH0AdicRingEquiv` はその後に `principalCompletionAdicAlgEquiv`。
    DerivedCompletion の中だけで使われていた PD 経由の 13 宣言（`completedAlgebraH0PD(B)AlgEquiv`・`completedTensorH0PDAlgEquiv(OfIso/OfTor/OfKoszul)`・
    `pdCompletionBaseAlgebra` ほか）を削除し、改名表（rename_2b.json）に「削除」として載せた。
  - B4a（f2339b603）：Pair/Iteration の `.choose` 4 か所を `pairCompletionLift`・`iteratedCompletionLift` に置き換えた。
  - **B4 の本体（Pair* の定義を Principal の反復へ移す、§3.5.3）は段階 3 へ回す**。BS は `PairCompletionH0` を Koszul の H⁰ として定義どおりに使っている
    （RootEnvelope/RawCompletion などで `koszulCompletionH0Unit Raw (pairKoszulCoordinates …)`、`pairKoszulCoordinates` は 16 回）。定義を反復の側へ移すと
    これらの証明が壊れ、条件 (ii) に触れる。段階 3 で BS と相談して、BS 側を `pairCompletionUnitRingHom` などの API 経由に書き換えてから行う。
  - **B4（段階 3、11-04、refactor/b4 278ad8b01）**：前提として 5ea6b3485 で `pairCompletionH0Unit` を置き、BS が 8 か所を置き換えた（f654244bb）。
    `PairCompletionH0` を一つの座標の完備化の反復 `IteratedCompletionH0` を `R` 加群として見たものに定義し直し、反映は Pair/Iteration で直接示した
    （一つ目の座標で完備な加群に一つ目の H⁰ の作用が入り、`R` 線形写像がそれを保つことから二度目の反映に帰着）。Pair/Tower と Pair/Koszul の行列模型
    （106 宣言、計 1,519 行の削除）を消した。API を述べた後で `PairCompletionH0`・`pairCompletionH0Unit` を irreducible にした（`irreducible_def` は強すぎる）。
    型が変わったのは `pdCompletionUnit_apply`（BS が使う、右辺を `pairCompletionH0Unit` に）と DerivedCompletion 内の `pairCompletionUnitRingHom_apply` だけ。
    新しい定義では一つ目の H⁰ の積が反映から選択で定まるため BS の単一化が重くなり、BS が maxHeartbeats を 3 か所で上げた（7c4e56d1b・23152a62c）。
    全ビルドと verify（1e15322b6、VERIFY_JOBS=6 VERIFY_MEMORY_GB=40、63 分）：ビルド 2/2・sorry 閉包 PASS、監査 101/102。失敗の 1 本 `audit_infinity_f1` は
    B4 と無関係で、`run_cmd` の `importModules` で読む F1/Diagrams の 15 本が監査対象の抽出（import 行のみ）から漏れて olean がなかったため。15 本を
    ビルドして単独で流し直すと PASS。
- 全ビルドと verify（11-04 08:37〜09:58、main cc67ea88e（BS-W10 作業 A を含む）を取り込んだ 48ec4a1b7 の上、VERIFY_JOBS=6 VERIFY_MEMORY_GB=40）：
  **PASS gate:true、監査 99/99、sorry 閉包 PASS**（ルート 447 秒、監査対象 759 秒、全体 79 分）。∞ の IF-W2c の内部ビルドが鍵を持っていたので 08:37 まで待った。
  改名表は 2b の分だけで宣言 23 件（2a から回した CLMST の一般部分 10 件と B3 の削除 13 件）、モジュール 116 件（DerivedCompletion 135 本のうち、残り 19 本は名前のまま）。
## G. 決定待ち

1. ~~段階 0 を CA の残りより先に行うか~~ → 先に行う（2026-10-30）。
2. ~~Mathlib を上げる時期~~ → この整理の間は上げない。最新版で直す必要がある箇所は H に記録する（2026-10-30）。
3. ~~Asymptotic~~ → (a) PaperQuotient（15 本）は Paper/Section4 へ移す。(b) 商の二本立ては論文の記述（Paper 側：Karoubi 完備化してから
   Verdier 商）を正にし、Completed 側の結果は比較の同型で導く（段階 3）（2026-10-30）。
4. ~~CategoryTheory~~ → (a) Nerve*（NerveHomotopy・NerveHomotopyUniverse・NerveSimplexEndpoint・NerveSimplexStart・NerveSimplexFirstFunctor・
   NerveVertices）と SimplexChainVertices・ElementsChainLifting・ElementsNaturalPrecomp を HomotopicalAlgebra/Simplicial の側へ移す。
   (b) 下位ディレクトリ（§1.3）の整理は ∞ 基盤の Codex の指示書に含める（伝達文を ∞ 基盤のレーンへ渡す）。(a) の移動も ∞ 基盤側で行う
   （利用者はすべて HomotopicalAlgebra・EInfinity・KST）（2026-10-30）。
   **∞ 基盤側の受け取り（2026-10-30、infinity-foundation-plan.md a6e58a0a3）**：R75 死んだファイルと殻の削除 29 本（IF-W0-4）、R76 Nerve 9 本を
   HomotopicalAlgebra/Simplicial へ（W2a）、R77 下位ディレクトリの統合 104 → 約 35 本（W2a）、R78 Mathlib への置き換え・未使用の削除・private 化・
   名前空間（段 G）。これらのファイルは論文の層の側では触らない。CategoryTheory のトップ階層の残り（Karoubi・三角圏・t 構造・K₀ など）は
   こちらの管轄。作業の前に互いの対象が import し合っていないかを確かめ合う。
   **import の確認（2026-10-30）**：こちら → ∞ 側は 1 件（FiniteBijectionInduction → Groupoid/ThinComponents）。∞ 側 → こちらは 5 件
   （Monoidal/MappingUnitLaws・AdjunctionCompositeNaturality → AdjunctionHomLaws、Monoidal/PowerBijectionFunctor → FiniteBijectionAction、
   Monoidal/TensorPowerBlockPermutations → FiniteBlockEquiv、Monoidal/PowerBijectionAppend → FiniteBijectionSum）。こちらが AdjunctionHomLaws を
   削除する（§1.2.2、Mathlib の `Adjunction.homEquiv_naturality_*` で足りる）ときと、FiniteBijection*・FiniteBlockEquiv を統合・移動するときは、
   ∞ 側の Monoidal/* の import を一緒に直すか、先に ∞ 側に伝える。
   **追加の移管（2026-10-30）**：CT のトップ階層のうち利用者が ∞ 側だけの 12 本（AdjunctionHomLaws・CommaIdentities・FiniteBijection・
   FiniteBijectionAction・FiniteBijectionInduction・FiniteBijectionShift・FiniteBijectionSum・FiniteBlockEquiv・FunctorTransport・
   ParametrizedAdjunctionTransport・PointwiseAdjunction・RelativeArrow）も ∞ 側へ渡した（伝達文 §7）。これで上の互いの import はすべて ∞ 側の中の依存になる。
   **∞ 側の受け取り（2026-10-30、infinity-foundation-plan.md 8093866b5）**：伝達文 §5 ComplexLimits は R63（W1。殻を実体で置き換え監査を再生成）、
   §6.1 GroupTheory/Coxeter は動かさず「中核より下の基盤」として layers.json に登録（Mathlib への置き換えは R78）、§6.2 Inputs/Homotopy は
   InfinityCategories/ModelBridge/Inputs/ へ移し許可リストと check のパスを直す（W2a、削除は台帳 R60 で判断）、§7 の 12 本は R77 の統合に加える
   （116 → 約 38 本、FunctorTransport・AdjunctionHomLaws の Mathlib への置き換えは R78）。両側の対象の間の import はなくなった。
   ArrowFactorization* の 3 本も ∞ 側（§1.2.2）。CT のトップ階層でこちらが扱うのは、論文の層が使う 67 本と、CT の中だけで使う 2 本
   （BoundedTStructureGeneration・SerreDerivedQuotient）。
5. ~~KTheory：dévissage 一式~~ → 残して軽くする（2026-10-30）。主定理 `g0QuotientDevissageEquiv : G₀(R ⧸ J) ≃+ G₀(V(J) に台をもつ加群)`。
   (1) DevissageAnnihilated の不要な import（K0LocalizationCoefficients、閉包 132 のうち 125）を外して G0Supported を直接 import する（段階 0 で先に）。
   (2) Mathlib への置き換え（`Module.isTorsionBySet_iff_subset_annihilator`・`LinearMap.annihilator_le_of_*`・`LinearMap.exact_subtype_mkQ`）、
   (3) 7 本を `KTheory/G0/Devissage` など 2 本程度に統合、(4) `chosenDevissageFlag` の def の形の整理、論文の主経路では使わないことを
   docstring に明記（KTheory の段階で）。
6. ~~PC・KTheory~~ → (a) 係数の定義（`SupportedCoefficients` など、K₀ の基底変換）を PerfectComplex 側へ下ろす（§4.5.1）。(b) K₀ のモデルは
   引用の文言を変えないよう `K0Supported` を残し、`K0WithSupport` との比較の同型で結ぶ。一本化が課題であることは `PerfectComplex/K0.lean` の
   docstring に書いた（§4.2.3）（2026-10-30）。

7. ~~GroupTheory/Coxeter と Inputs/Homotopy/~~ → ∞ 基盤の側へ渡す（2026-10-30。伝達文 §6）。Inputs/DifferentialGraded/ も dg の側。
8. Paper（第 10 章）：(a) 主経路から外れたもの（§10.2）→ (iii) 古い正値性の経路 AsymptoticPositivity・SecondComparisonLowerBound は削除
   （区切り 0 の追加分。Asymptotic 側に連鎖はない）。(ii) 変種 ParameterQuotientCM・FlatRealization は残す（FlatRealization が使う
   Asymptotic/PaperVanishing も残る）。(i) 論文の番号付きの主張（Theorem4_7・Corollary2_6・Lemma3_4・Lemma2_4）は残し、主経路をこれらにつなぎ直して
   重複を消す（提案。区切り 1-4 の前に確認）（2026-10-30）。(b) ~~ディレクトリ名~~ → Section2〜5 は
   論文の節に合わせて残す（C の規約の例外、2026-10-30）。ファイル名は内容の名前、論文の番号は docstring に書く。

9. ~~CLMST の Claim 2.4.8（§8.2.3）~~ → (a)：一般形（FiniteFreeConeIsogeny）を HA へ下ろし、論文側（Prop247/ConstantRank 付近）に Claim 2.4.8 の
   薄い入口（一般形を論文の記号で言い直すだけ）を残す。使い手のない有限代数版 `finiteAlgebraConeIsogeny` は削除する（2026-10-30）。

## H. 最新の Mathlib で直す必要がある箇所（記録）

この整理は固定版の Mathlib で行う。作業中に、最新版に上げたときに直す必要がある箇所や、最新版で置き換えられる箇所に気づいたら、ここに追記する。
群に着手するときは、触るファイルについて最新版の対応する名前を grep で確かめる。

| 箇所 | 最新版での変化 | 対応 | 記録日 |
| --- | --- | --- | --- |
| HomologicalAlgebra/StupidTruncation（`above`・`below`・`inclusion`・`projection` ほか） | `HomologicalComplex.stupidTrunc`・`ιStupidTrunc`・`πStupidTrunc`・`isIso_ιStupidTrunc_f`・`ιStupidTruncNatTrans` が入った | 置き換えて削除（§3.2.2）。CT の TruncationTriangle の import も外れる | 2026-10-30 |
| CommutativeAlgebra/RegularLocalRing | `IsRegularLocalRing` の定義（RegularLocalRing/Defs）が入った（整域性・商の定理はまだない） | 自前の定義との一致を確かめ、Mathlib の定義へ寄せる | 2026-10-30 |
| CategoryTheory/LiftingProperties/Under・MorphismProperty/UnderFactorization | Mathlib の名前空間（`CategoryTheory.CommSq.HasLift.under` など）に直接置いている | 上げたときに名前の衝突がないか確かめる（§1.3.5） | 2026-10-30 |

## 第1章 CategoryTheory

### 1.1 外への影響

- BhattScholze が使うのは `ExactDerivedTStructure` の 1 本だけ（BS/Almost/PerfectoidAlmost が `derived_isZero_iff_homology` を使う）。
  名前と、その import の閉包を残す。CLMST は CategoryTheory を import しない。
- トップ階層（§1.2）の利用者は論文の層全般（Asymptotic・PerfectComplex・KTheory・LengthAlgebra・Paper）。
- 下位ディレクトリ（§1.3）の利用者は Spectra・HomotopicalAlgebra（主に `HomotopicalAlgebra/GeneralTools` の再エクスポート経由）・EInfinity・KST。

### 1.2 トップ階層（102 → 約 30 ファイル）

#### 1.2.1 統合

| 新しいファイル | 元のファイル |
| --- | --- |
| Karoubi/Basic | KaroubiLinear・KaroubiShift・KaroubiFullyFaithful・KaroubiImage |
| Karoubi/Triangulated | KaroubiPretriangulated・KaroubiTriangulated・KaroubiTriangulatedFunctor・KaroubiExtensionOne・KaroubiHomological（Balmer–Schlichting） |
| Triangulated/Idempotent | TriangleIdempotent・TriangleIdempotentCompletion・CubicConjugation・ThreeComponentMaps |
| Triangulated/Padding | TriangleBiproduct・TrianglePadding・OctahedronBlockRetract・OctahedronPadding・OctahedronEssentialImage |
| Triangulated/VerdierLift | CommShiftOfPrecomp・VerdierLift・HomologicalLocalization・SubcategoryLinear |
| Triangulated/VerdierKaroubi | VerdierKaroubi・VerdierKaroubiLinear |
| TStructure/Basic | TStructureHeart・TStructureRetracts・TExactTruncation |
| TStructure/Bounded | BoundedTStructureIdempotent・BoundedTStructureGeneration |
| TStructure/Localization | LocalizationTStructure・VerdierTStructure・TExactKernelQuotient・HomologicalKernelTStructure |
| TStructure/Family | FamilyTStructure・FamilyTriangulatedImage |
| Derived | DerivedPure・ExactDerivedTStructure・SerreDerivedQuotient（ExactDerivedTStructure は BS が使うので、閉包を重くしないよう別に残す案も） |
| Abelian/SerreLength | SerreSubcategory・SerreLength・AdditiveLength |
| Abelian/ShortComplex | ExactImageSequence・ExactRetract・ShortExactCokernel |
| TriangulatedK0 | TriangulatedK0・TriangulatedK0Shift |
| Euler | HomologicalEuler・EulerComparison・ExactSequenceEuler |
| IteratedCone | HomologicalConeLength・IteratedCone・ScalarZeroCone |
| ScalarSupport（2 本） | ScalarSupport*・SemilinearScalar・KaroubiScalarSupport |
| BoundedHomotopy | BoundedHomotopy・BoundedHomotopyGeneration・TruncationTriangle |
| HomotopyProperty | HomotopyProperty・HomotopyConeRepresentative・FullSubcategoryTriangle |
| Nerve | NerveHomotopy・NerveHomotopyUniverse（§1.2.3）・NerveSimplexEndpoint・NerveSimplexStart・NerveSimplexFirstFunctor・NerveVertices |
| Simplex/Chains | SimplexChainVertices・ElementsChainLifting・ElementsNaturalPrecomp |
| FiniteBijection（2 本） | FiniteBijection*（Spectra・Monoidal・EInfinity だけが使う） |
| Adjunction | ParametrizedAdjunctionTransport・PointwiseAdjunction（AdjunctionHomLaws は削除、§1.2.2） |
| Arrow | RelativeArrow・CommaIdentities（ArrowFactorization* は Mathlib へ、§1.2.2） |

- 圏論でないものを外へ：AlternatingSum（ℤ → ℝ の finsum）・FiniteSupportBounds（`Function.HasFiniteSupport` の補題 1 つ）・ConeLengthBinomial・
  ConeLengthCancellation（ℤ → ℝ の二項係数の演算子の計算）→ 一般の補題のファイル（Mathlib 形式）へ。WellFoundedHistory（順序・論理、
  唯一の利用者は CA/ResidueFieldExtension）→ そちらへ。FiniteBlockEquiv（`Fin` の同値）→ FiniteBijection の近く。
- 層の逆転：
  - ScalarSupport が HomologicalAlgebra/NullHomotopy を import しているのは一般の線形圏の補題 2 つ（`smul_mul_self_id_eq_zero`・
    `pow_smul_id_eq_zero_of_le`）のため。その 2 つを CategoryTheory（SemilinearScalar）へ下ろす。
  - TruncationTriangle が HomologicalAlgebra/StupidTruncation を import（StupidTruncation の Mathlib 化は保留中、§3.2.2）。
  - EulerComparison が GroupTheory/ConjugateSum を import。
  - NerveVertices が HomotopicalAlgebra/Simplicial/VertexTuples を、NerveSimplexFirstFunctor が HomotopicalAlgebra/Simplicial/SimplexNerveAugmentation
    を import し、後者は CategoryTheory/SimplexChainVertices を import する（ディレクトリをまたいだ循環に近い）。∞ 基盤の計画と合わせて、
    Nerve*・Simplex/Chains を HomotopicalAlgebra/Simplicial 側へ移すか、逆に VertexTuples を下ろすかを決める。
  - 再エクスポートの殻 7 本が HomotopicalAlgebra/Rectification を import（§1.2.4 で削除）。

#### 1.2.2 Mathlib との重なり（確度高のもの）

- `FunctorTransport.transport`・`iso`・`transport_obj`・`iso_hom_app` = `Functor.copyObj`・`isoCopyObj`（NatIso）。ファイルごと削除。
- **ArrowFactorization* の 3 本（2026-10-30）**：利用者はすべて ∞ 基盤の側（HomotopicalAlgebra/GeneralTools・Rectification/CategoryTheory/AnchoredChain*）
  なので ∞ 基盤の側へ渡す（ユーザーの決定。受け渡しと docstring の旧計画への参照の書き換えはユーザー側で扱う）。論文の層の側では触らない。
  下の Mathlib の `Factorisation` への置き換えの記録は ∞ 側への申し送り。
- ArrowFactorization・ArrowFactorizationCategory（`source_isInitial`・`target_isTerminal`）≈ `CategoryTheory.Factorisation`（`initial`・`terminal`・
  `IsInitial_initial`・`IsTerminal_terminal`）。宇宙の扱い（Mathlib は hom の宇宙が `max u v`）に注意して置き換える。
- `triangle_isIso_of_components` = `Triangle.isIso_of_isIsos`。
- `triangleBiproduct_distinguished` は `productTriangle_distinguished` の薄い系として書き直す（確度中〜高）。
- AdjunctionHomLaws：`*Law : Prop` とその補題はどれも `Adjunction.homEquiv_naturality_left/right`・`Equiv.left_inv/right_inv`・`homEquiv_unit`
  の言い直し。`comparisonHomEquiv` ≈ `a.homEquiv … |>.trans (e.homCongr …)`。ファイルごと不要。
- HomologicalLocalization は `Functor.mem_homologicalKernel_trW_iff` の 5 行の包み、ShortExactCokernel は
  `(cokernelIsCokernel _).coconePointUniqueUpToIso hS.gIsCokernel`（`Adams.` の別名つき）。インライン化。
- VerdierLift は `Localization.lift`・`commShiftOfLocalization`・`Functor.IsTriangulated` の補題で大部分が作れる（確度中）。
  `commShiftOfPrecomp`（前合成の版）は Mathlib にない（`Functor.CommShift.ofComp` は後合成の版）。
- Mathlib にないもの：三角圏の Karoubi 完備化（シフト・pretriangulated・triangulated）、Karoubi の `Linear`、ハートのインスタンス（abelian・
  `ContainsZero`・有限積）、t 構造の retract での安定性、局所化への t 構造、三角圏の K₀、有界ホモトピー圏、自然変換から脈体のホモトピー、
  `Exact.of_retract`、`P.isoModSerre.Localization` の Abelian インスタンス。

#### 1.2.3 一本化

- NerveHomotopy と NerveHomotopyUniverse はほぼ同じ（後者は `ULift` で宇宙を独立にしたもの）。一般の版から同じ宇宙の版を導く。
- NerveSimplexEndpoint と NerveSimplexStart は双対（`tail` と `initialSegment`）。一つの構成に。
- `localizationTStructure` と `verdierTStructure`（後者は前者の特殊化）。`*_isIdempotentComplete`・`*_has_representative`・`*KaroubiEquivalence`
  が 4 回（BoundedTStructureIdempotent・LocalizationTStructure・VerdierTStructure・TExactKernelQuotient/SerreDerivedQuotient）。
- Asymptotic・LengthAlgebra・Paper の `*EulerK0 : TriangulatedK0 … →+ ℝ` は `homologicalEulerK0`・`TriangulatedK0.lift` の型の繰り返し
  （§7.5）。
- `DerivedPure.derivedPureHomologyIso` は `Classical.choice` でデータを作っている。HA の `normalizedPureHomologyIso`（同じく `.choose`）と
  一本化し、明示的な構成にする（§3.3.5）。

#### 1.2.4 死んだファイル・未使用

- 死んだファイル：再エクスポートの殻 7 本（AnchoredChain*・ArrowContext・LabelledChain・SimplexChainParameter。importer は
  `scripts/audit/shared.lean`・`scripts/audit_homotopical_foundations.lean` だけ）、EulerTheory（ルートと scripts だけが import する集約ファイル）。
- 未使用の宣言（instance を除く）：`additiveLength_le_of_retract`、AdjunctionHomLaws の 4 つ、`pre_post_transport`、`essSurj_of_bounded_of_heart`、
  `boundedSubcategory_isIdempotentComplete`・`boundedTStructureKaroubiEquivalence`・`karoubi_bounded_has_representative`、
  `coneLength_binomial_homological`、FunctorTransport の 3 つ、`homologicalEuler_natIso`・`homologicalEulerK0_unique`・`homologicalEulerK0_pullback`、
  `iteratedZeroCone_iso`・`iteratedZeroCone_length_lower_bound`、`karoubi_smul_f`（simp）、KaroubiShift の simp 補題、
  `exists_tExact_localizationTStructure_iff`、`serreDerivedQuotientKaroubi_has_bounded_complex`、`serreQuotientLength_obj`（simp）、
  `heart_isIdempotentComplete`、`karoubi_pure_has_representative`、`completedKaroubiFirstToLast_isEquivalence`、`verdierTStructure_le/_ge`・
  `verdierKaroubiEquivalence`。simp の補題は消す前にビルドで確かめる。

#### 1.2.5 その他

- 一般的すぎる名前が裸の `SerrePositivity` 名前空間に多い（`conjugate_cube`・`conjugate_projection`・`section_sum0/1/2`・
  `three_components_rotation`・`idempotent_cubic`・`biprodDescComp`・`heart_containsZero`・`familyMap`・`familyFunctor`・
  `finiteSupport_of_bounded_zero`・`alternatingFinsum_*`・`pure_mem_of_heart`・`bounded_le_of_heart`・`localization_hom_eq_zero` など）。
  `SerrePositivity.Triangulated`・`.TStructure`・`.Karoubi` に入れる。
- `def …Law : Prop` で等式を包む書き方（AdjunctionHomLaws、§1.3 の Monoidal の多く）はやめ、補題の主張に直接書く。
- VerdierKaroubi の `synthInstance.maxSize 512`、約 30 ファイルの `backward.*` の移行用オプションは、統合のときに外せるか試す。

#### 1.2.6 提出候補（価値の高い順）

三角圏の Karoubi 完備化（シフト・Linear・pretriangulated・triangulated、八面体は padding で）、ハートのインスタンス、t 構造の retract での安定性と
有界なら冪等完備、Verdier 局所化への t 構造、前合成についての `Functor.CommShift`、自然変換から脈体のホモトピー、`ShortComplex.Exact.of_retract`、
`P.isoModSerre.Localization` の Abelian、三角圏の K₀（`mk_shift`）、有界ホモトピー圏、`ParametrizedAdjunction.restrict`。

### 1.3 下位ディレクトリ（104 → 約 35 ファイル。利用者は ∞ 基盤の側だけ）

（2026-10-30 に ∞ 基盤の側へ移管した（R75〜R78）。以下は引き渡したときの調査の記録で、正本は ∞ 基盤の計画。）

#### 1.3.1 死んだファイル

- Presentation/ の 15 本すべてと Quiver/WeightedPaths・WeightedPathMaps：各 24 行で、同名の `HomotopicalAlgebra/Rectification/CategoryTheory/…`
  を再エクスポートするだけ。importer なし、ルートにもない。参照は `scripts/homotopical_generalization_manifest.json` だけ。削除してマニフェストを直す。
- Spectra/SymmetricSequence の殻 4 本（TensorPowers・TensorPermutations・AdjacentTranspositions・AdjacentBraid、各 10 行で Monoidal/* を再エクスポート）。
  importer を張り替えて削除。

#### 1.3.2 統合

| 新しいファイル | 元のファイル |
| --- | --- |
| Monoidal/Mod/Free | FreeModule |
| Monoidal/Mod/Limits | ModuleLimits・ModuleColimits・ModuleTransport |
| Monoidal/Mod/BalancedTensor | BalancedTensor・BalancedTensorModule・BalancedTensorIterated・TensorRightModule |
| Monoidal/Mod/Monoidal | BalancedTensor{Associator,LeftUnit,RightUnit,Triangle,Pentagon,Monoidal} |
| Monoidal/Mod/Symmetric | BalancedTensor{Symmetry,Hexagon,Symmetric} |
| Monoidal/Mod/FreeTensor | BalancedTensorFree{Left,Right,Pair,Unit,Associator}・FreeModuleMonoidal |
| Monoidal/Mod/InternalHom | ModuleInternalHom・…Action・…Functor |
| Monoidal/Mod/InternalHomFree | ModuleInternalHomFree*・…Transport* |
| Monoidal/Mod/Closed | ModuleClosed |
| Monoidal/TensorPower/Basic | TensorPowers・TensorPowerCoherence |
| Monoidal/TensorPower/Permutation | TensorPermutations・AdjacentTranspositions・AdjacentBraid・PermutationAction |
| Monoidal/TensorPower/Blocks | TensorPowerBlockGenerators・LeftBlock・BlockPermutations・FirstCrossing・FirstCrossingAction |
| Monoidal/TensorPower/FinBijection | PowerBijectionFunctor・PowerBijectionAppend |
| Monoidal/Action | ActionProductComparison・TensorActionTransport |
| Monoidal/Braided | BraidingPreservation・InternalHomExchange |
| Enriched/RepresentedMapping | Mapping{Adjunction,ParametrizedAdjunction,UnitLaws,Associativity,ArrowComposition,Whiskering}・RepresentedMappingEnrichment・RepresentedHomFunctor（今は Monoidal/ にあるが中身は豊穣圏） |
| Enriched/Transport | TransportOrdinaryEnrichment・TransportEnrichmentComparisons・LaxPointHom・ReverseComposition |
| Enriched/Simplicial | SimplicialHomLaws |
| Enriched/TensorCotensor | TensorCotensor・TensorUnit・EnrichedRepresentability |
| Adjunction/Comparison | ActionComparisonAdjunction・ActionUnitAdjunction・ActionComparisonNaturality・AdjunctionCompositeNaturality・HomEquivNaturality（モノイダル構造を使わない） |
| Quiver/FreePathComonad | FreePathComonad・PathObjectTransport |
| Quiver/PathMap | PathIntersections |
| Simplex/Prefix | Prefix・PrefixInterval |
| Simplex/GenRelEquivalence | PresentationDegeneracies・PresentationFaces・PresentationEquivalence（約 470 行） |
| Simplex/Naturality | Naturality（§1.3.3 で中身の大半は Mathlib へ） |
| Under | LiftingProperties/Under・MorphismProperty/UnderFactorization |
| Limits | Limits/InitialColimits・Limits/SequentialExtension・LiftingProperties/ParametrizedGeneration・Groupoid/ThinComponents |

#### 1.3.3 Mathlib との重なり

- `QuiverPaths.natTransOfEdges`（Quiver/PathNatTrans）= `Paths.liftNatTrans`（確度高、そのまま置き換え）。
- `functor_ext_edges`・`prefunctor_hext`（Quiver/PathFunctorExt）= `Paths.ext_functor`（HEq の代わりに eqToHom、確度高）。
- Quiver/FreePathComonad の `comonad` ≈ `Quiv.adj : Cat.free ⊣ Quiv.forget` の `.toComonad`（確度中〜高）。`mapPath` ≈ `Prefunctor.mapPath`（確度中）。
- `Simplex/Naturality.property` = `MorphismProperty.naturalityProperty`、証明は `SimplexCategory.morphismProperty_eq_top`（確度高、def は不要）。
- `rightIso`（ActionComparisonAdjunction）・`rightUnitIso`（ActionUnitAdjunction）は `(a.ofNatIsoLeft e).rightAdjointUniq b`（確度高、インライン化）。
- 豊穣化の作用 `H : V ⥤ D ⥤ D` と `a : H(P⊗Q) ≅ H Q ⋙ H P` は `MonoidalRightAction` で書き直せる見込み（確度中）。Transport* は
  `TransportEnrichment`・`enrichedOrdinaryCategory` と重なる（確度中）。
- Mathlib にないもの：`SimplexCategoryGenRel ≌ SimplexCategory`（Mathlib に明示の TODO）、可換モノイド対象上の `Mod` の自由加群・極限・余極限・
  balanced tensor・対称モノイダル閉構造（Mathlib の `Mod` は圏と `regular`・`forget`・`comap` だけ）、Under 版の持ち上げ性質・分解、
  細い亜群と成分の同値。Presentable・Day convolution は Mathlib（固定版）にあるが、ここでは使っていない（Presentation/ は語の表示の話）。

#### 1.3.4 未使用

Enriched/TensorCotensor の自然性 5 つと `cotensor_triangle`、`unitMap_isIso`、SequentialExtension の `stage_zero`・`descend_zero`、
BalancedTensor 系の `_hom`・`_inv` の補題約 15、`freeHomIso_naturality_left`・`freeHomObj_action_formula`、`homBifunctor_map`、
ModuleTransport の `iso_inv`・`obj_action`、`comparison_inv_naturality`、`mapPath_singleton`、`ofFacesDegeneracies_app`、`standardδ_comp`・
`standardδ_nil`。ファイルの中だけで使われている約 120 の名前は private に。

#### 1.3.5 その他

- 104 本のうち 55 本が `backward.isDefEq.respectTransparency false`（と `.types false`）を設定（Mod の一群と Quiver の全部）。外せるか試す。
- ファイル名の名前空間（`SerrePositivity.HomEquivNaturality`・`.ReverseComposition`・`.LaxPointHom` など）に一般的な名前（`derived`・`pre`・
  `parameter`・`identity`・`composition`・`points`・`left_action`・`map`）が入っている。Limits/InitialColimits は裸の `SerrePositivity` に宣言。
  LiftingProperties/Under・UnderFactorization は Mathlib の名前空間（`CategoryTheory.CommSq.HasLift.under` など）に直接置いている
  （提出の準備としてはよいが、Mathlib を上げたときに衝突しうる）。
- Quiver/・Simplex/ の docstring が同じ定型文（「分類A」「生成辺と空の道…」）の繰り返し。

#### 1.3.6 提出候補（強い順）

1. `SimplexCategoryGenRel ≌ SimplexCategory` と P_δ の一意な標準形（Mathlib の TODO を埋める）。
2. 自由 `Mod` ⊣ forget、`Mod.forget` が極限・余極限を作る、可換 M についての `Mod C M` の対称モノイダル閉構造。
3. LiftingProperties/Under・MorphismProperty/UnderFactorization（Over 版の双対、小さく準備済み）。
4. Limits/InitialColimits、Groupoid/ThinComponents。
5. 対称モノイダル圏のテンソル冪への `Equiv.Perm (Fin n)` の作用。
6. `map_braiding_tensor_left`（BraidingPreservation）。

### 1.4 章の中の作業順

1. 死んだファイル（§1.2.4 の 8 本、§1.3.1 の 21 本）と確度高の Mathlib への置き換えを先に（BS/CLMST の波及なし。Presentation の殻はマニフェストだけ）。
2. トップ階層の統合（§1.2.1）。BS が使う ExactDerivedTStructure の閉包は変えない。
3. 下位ディレクトリ（§1.3）・Nerve まわりは ∞ 基盤の側へ移管済み。

決定済み（G の 4）：Nerve まわりは HomotopicalAlgebra/Simplicial へ、下位ディレクトリの整理は ∞ 基盤の指示書で行う。

## 第2章 CommutativeAlgebra

（元の計画の §2 作業の決まりは前半の A へ移し、完了した C3・B1・B2 の §3〜§5 は省いた。節番号は元のまま。）


### 2.1 状態

| 群 | 内容 | 状態 |
| --- | --- | --- |
| G（G1〜G7） | 冪級数・導分・完備微分・p 基底の持ち上げ・Cohen–Gabber | 完了（bfec81e21 ほか、G7 は 612eae3e3） |
| A（A1〜A6） | adic 完備化 | 完了（f00bad23f・9c41f5f43、abd87dba6・1ed27fe56・cdbefbde9） |
| F（F1〜F4） | 係数体・剰余体拡大・Witt | 完了（9bce1e872・7df4d71bd、audit_f5 は 93d84541e） |
| C1 | 正則列と深さ | 完了（RegularSequence・Depth・Unmixedness・MaximalRegularSequence、候補 G9） |
| C2 | パラメータ系 | 完了（SystemOfParameters/{Basic,Existence,Generators,Finite,Avoidance}、候補 G10） |
| C3 | 正則局所環 | 完了（RegularLocalRing/、HenselianFinite、候補 G11。RegularBaseChange の 2 補題は CLMST の証明が使うので RegularSequence へ移して保持） |
| B1・B2 | Hilbert–Samuel・長さ・Koszul・重複度 | 完了（7242dc7f7、CLMST 側 e0308bb75。全依存ビルドと監査を通した） |
| D・E・H・X | 残り | 計画（§2.6〜§2.9） |

C1〜C3 は一回の全依存ビルド（388 モジュール）と監査を通してコミットした（2026-10-30）。


### 2.6 E 局所化

規模：21 ファイル、約 2300 行。CLMST 約 25 本の import、BS は 1 宣言（`existsUnique_valuation_extension_of_integral_away_bijective`）。

新しいディレクトリ `CommutativeAlgebra/Localization/`。

| 新しいファイル | 元のファイル |
| --- | --- |
| PowerTorsion | LocalizationPowerBound・LocalizationComparisonBounds・LocalizationTorsion・LocalizationInverse・PrincipalCoverNumerators の一様冪の補題 |
| Lattice | LocalizationLattice |
| CommonModel | FiniteCommonLocalizationModel・FiniteCommonLocalizationBounds・FinitePresentationCommonLocalizationModel・FinitePresentationCommonLocalizationBounds・LocalizationComparisonTensorEquiv |
| FiniteAlgebraLift | FiniteAlgebraLocalizationLift |
| Away | PrincipalLocalizationNormalization・DoubleLocalizationTensorComparison・PrincipalCoverNumerators の残り・IntegralAwayExtension・GenericEtale の `awayAlgebra`（一般の可換環で成り立つので移す。GenericEtale が Away を import する向きにして循環を避ける） |
| EtaleAway | EtaleAwayBaseChange・EtaleAwayTensorBaseChange |

- 外へ回す：CoprimeFactorLocalization・LocalizedSurjectiveQuotient → CubicCyclotomic（X）。SemilocalSupport → KTheory（E では動かさず、KT1 の G0/SemilocalSupport で SupportHeight・ModuleSupportHeight と一緒に移す）。LocalizationTelescope → Adic か HomologicalAlgebra/DerivedCompletion。
- Mathlib への置き換え：`IsModuleSTorsion P M` → `Module.IsTorsion' M P`（`iff_localized_zero` は `LocalizedModule.subsingleton_iff`、`iff_tensor_zero` は `IsLocalizedModule.subsingleton_iff`。波及は KTheory 5 本・ModuleSupport・InfinityCategories で BS/CLMST なし）。`exists_pow_smul_zero_of_localized_zero` → `IsLocalizedModule.Away.exists_of_eq`（確度高）、`localizationComparison_ker_power_torsion` もほぼ 1 行。`exists_clear_denominators` → `Module.FinitePresentation.exists_lift_of_isLocalizedModule`。`isLocalizationLattice_span` → `IsLocalization.mem_span_iff`。`IsLocalizationLattice.tensorEquiv` は `IsLocalizedModule.isBaseChange` の包み。`principalLocalizationTower_scalarTower` は `inferInstance`。`awayModuleMap` は `LocalizedModule.map (.powers g) f` と同じと見込まれる（CLMST 10 本が使うので名前は残し、定義の一致をビルドで確かめる）。`existsUnique_valuation_extension_of_integral_away_bijective` は ValuationRing → IsIntegrallyClosed のインスタンス連鎖で一般版だけで足りる見込み（BS が参照）。
- 一本化：一様冪の補題 3 本（任意の乗法的集合の版を本体にし、`exists_uniform_pow_smul_zero` の名前を残す）。共通模型の証明の前半 4 回の重複を `localizationSplitting_maps` と 2 つの instance に括り出す。共通冪の補題 2 本。ker 側の補題を任意の乗法的集合に一般化。EtaleAway を `[IsLocalization.Away g Rg]` の形に（CLMST への波及が大きいので後回し）。
- 未使用：`principalSplitting_exists_finite_common_model`、`principalLocalizationTower_algebraMap`、`principalLocalizationTowerEquiv`、`localizationSplitting_common_model_tensor_squares`、`exists_uniform_pow_smul_zero_of_localization`、`HeightAtLeast.localizedMaximalPointsEquiv`、`IsModuleSTorsion` の補題 7 つ。内部専用のもの（CoprimeFactorLocalization の中間補題 10 個など）は private に。残す価値あり：`localizationComparisonTensorEquiv_tmul`（`@[simp]` を付ける）、`localizationComparisonAwayEquiv`、`isLocalizedModule_of_comparison_power_torsion_coker`。telescope の simp 補題は audit_clmst が名前を書いているので残す。
- 変えない名前：`awayModuleMap`、`exists_uniform_pow_smul_zero`、`etaleAway_tensor_baseChange`、`doubleLocalizationTensorEquiv*`、`principalLocalizationTower_isLocalization`、`localizationComparison_awayMap_bijective_of_power_bounds`、`localizationComparison_ker_power_torsion`、`existsUnique_valuation_extension_of_integral_away_bijective`。
- 提出候補：`finiteAlgebra_exists_away_lift`（有限表示な代数から局所化への写像を主局所化まで下ろす。価値が高い）、有限生成な `Module.IsTorsion'` は一元で零化、`isLocalizedModule_of_comparison_power_torsion_coker`、`IsLocalizationLattice`、localization telescope、`existsUnique_extension_of_integral_away_bijective`、`principalLocalizationTower_isLocalization`。

決定（2026-10-30）：

1. `IsModuleSTorsion` は廃止して `Module.IsTorsion'` に置き換える（案 a）。KTheory 5 本・ModuleSupport・InfinityCategories の参照を書き換える。
   ∞ 側の InfinityCategories/Derived/Localization の参照もコーディネータが書き換え、∞ 側に対応表を伝える（2026-10-30、(i)）。
2. `awayModuleMap` は名前を残し、定義を `LocalizedModule.map (.powers g) f` の abbrev にする。
3. EtaleAway の `[IsLocalization.Away g Rg]` 形への書き換えは E の中で今やる。ただし CLMST は `hetaleB` を型の中で使う
   （`prop247_rankSourceImage … hetaleB n` など）ので、既存の主張は変えない。一般形（任意の `IsLocalization.Away` の
   模型の上の定理）を新しく立て、`etaleAway_tensor_baseChange`・`etale_away_baseChange`・
   `etale_away_of_mem_span_singleton`・`etale_away_baseChange_of_mem_span_singleton` はその特殊化として名前と主張を残す。
   CLMST（7 本 + NonunitIsogeny・TensorIsogeny）は書き換えない。
4. `existsUnique_valuation_extension_of_integral_away_bijective` は名前を残し、証明を一般版からの導出にする。


### 2.7 D 平坦性・降下・同種写像・冪等元

規模：35 ファイル、約 3100 行。BS 約 20 本・CLMST 約 15 本の import。

| 新しいファイル | 元のファイル |
| --- | --- |
| Adic/Reduction | AdicFaithfulDescent・AdicFaithfulDescentAlgebra・PrincipalAdicFaithfulDescent・PrincipalAdicReductionAlgebra・PrincipalAdicReductionEquiv |
| Adic/ReductionScalarExtension | QuotientScalarExtension（HomologicalAlgebra.BaseChange に依存するので別） |
| CompletelyFlat/Basic | CompletelyFlat・CompletelyFlatEquiv |
| CompletelyFlat/PowerTorsion | CompletelyFlatPowerTorsion・CompletelyFaithfullyFlatPowers・CompletelyFaithfullyFlatTensor・CompletelyFaithfullyFlatInjective |
| CompletelyFlat/Criterion | CompletelyFlatCriterion・CompletelyFlatNilpotent |
| ScalarIsogeny | ScalarIsogenyInverse・ScalarIsogenyTensor・FiniteFreeScalarFactorization・FiniteProductIsogeny・ReducedFiniteFreeIsogeny・FinitePresentationIsogenyLift・PullbackAnnihilator |
| Idempotent | IdempotentAnnihilator・IdempotentImageAnnihilator・IdempotentImageBaseChange・ProductIdempotentQuotient |
| TensorProduct/BaseChange | FiniteProductBaseChange・TensorRingEquiv・PresentationBaseChange |

- 層の順序は Adic/Reduction → HomologicalAlgebra → CompletelyFlat/{Basic,PowerTorsion} → CompletelyFlat/Criterion。Adic/Reduction と Criterion を同じファイルにすると、HomologicalAlgebra の DerivedQuotientBaseChange・RegularPrincipalTor を経て循環する。
- 決定（2026-10-30）：(1) 統合は表のとおり。(2) `adicQuotientAlgebra` の Mathlib の instance への置き換えは区切り 2a に回さず今行う。(3) 降下定理は
  一般イデアル版を本体にし主元版を系に。(4) Mathlib への置き換えは BS が使う名前（`quotientTensorReductionEquiv` など）も本体を差し替える（名前は残す）。
  (5) 未使用は提出候補（`surjective_of_faithfullyFlat_adicReduction`・`isCompletelyFlat_nilpotent_iff_flat`）を残して削除。BS の証明は必要な範囲で
  修正してよい（ユーザー許可、BS 分は独立コミットで変更箇所の一覧を付ける）。
- 外へ回す：SeparableBaseChange → FieldTheory（FractionRingBasis と組む）。GenericEtale → エタール（E の Away と調整）。GeometricFiber・GeometricTransitivity → Galois・不変元（`Inputs/Descent` の近く）。FlatTensorFiltration → Adic/Completion。FlatRegularQuotient → 正則列。FinitePresentationTorsionCover・PresentationBaseChange → PowTorsion・LengthAlgebra 寄り。
- 降下定理の扱い（以前の方針「PrincipalAdicFaithfulDescent は並行コピーなので除去」は実態と合わない）：使われているのは主元版（`surjective_algHom_of_principal_residue_baseChange` を BS/Semiperfectoid/Surjectivity が使用、`principalAdicQuotientAlgebra` 52 件など）で、一般イデアル版の定理は外部参照 0 件。降下定理は一般イデアル版 1 本にし、主元版を `Ideal.map_span` を介した系にする。`principalAdicReductionEquiv` は `adicReductionEquivAlgebraQuotient ≪≫ Ideal.quotientEquivAlgOfEq` として定義する。
- Mathlib への置き換え（固定版と最新版に差なし）：`adicReductionMap` → `LinearMap.reduceModIdeal`（確度高、BS/CLMST の参照なし）。`adicQuotientAlgebra` は Mathlib の instance `Ideal.Quotient.algebraQuotientMapQuotient` と定義が同じ（BS 35 件なので deprecated な別名を経由）。`ker_pi_eval_eq_span_one_sub_single` → `RingHom.ker_evalRingHom`。`ideal_map_isIdempotent` → `IsIdempotentElem.map` と `Ideal.mapHom`。`tensorMapOfCompatibleBase` → `Algebra.TensorProduct.mapRingHom`。`quotientTensorReductionEquiv` は `quotTensorEquivQuotSMul` の `extendScalarsOfSurjective`（名前は残し本体を差し替え）。自前の `map_smul'` の証明 4 つ → `extendScalarsOfSurjective`。`baseChangeQuotEquiv` → `TensorProduct.AlgebraTensorModule.tensorQuotientEquiv` から作る（確度中）。`baseChangeIdealQuotientEquiv` はインライン化候補。
- 一本化：`exists_scalar_factorization_through_finiteFree` は `exists_scalar_inverse_of_ker_coker_annihilated` の特殊例。逆向きの一般補題を立てて `tensor_unit_ker_coker_annihilated` を短く。冪ねじれの仮定を `Module.IsTorsionBy` に統一（D3・D5・D6）。IdempotentImageAnnihilator の 4 変種を 2 つに、IdempotentImageBaseChange の 4 補題を 1 つに。`exists_free_quotient_powTorsion_cover` と ModuleCat 版を 1 つに。`tensorAction_mul`・`_one` を `MulSemiringAction` の instance に（確度中）。
- 未使用：`surjective_algHom_of_residue_baseChange`（確認済み）、`surjective_algHom_of_faithfullyFlat_adicReduction`、`surjective_of_faithfullyFlat_adicReduction`（提出候補として残す価値）、`adicReductionMap_comp_mkQ`、`adicAlgebraReductionMap_equiv`、`principalAdicReductionAlgEquiv_toAlgHom`、`power_torsion_lTensor_*`・`power_residue_lTensor_*` の 4 つ、`isCompletelyFlat_principal_ideal_pow`、`isCompletelyFlat_nilpotent_iff_flat`（提出候補）、`flat_of_acyclic_flat_nilpotent_reduction`、`ideal_annihilates_of_pow_annihilates_*` 2 つ、`finrank_perfectBaseChange`、`tensorMapOfCompatibleBase_tmul`、`tensorRingEquivOfCompatibleBase_tmul`。`@[simp]` 4 つは残す。audit_clmst だけが参照：`exists_finite_etale_away_of_separable_minpoly`、FlatTensorFiltration の中間補題 4 つ。
- 変えない名前：`IsCompletelyFaithfullyFlat`（BS 114 件）、`IsCompletelyFlat`、`GenericEtale.awayAlgebra`（CLMST 82 件）、`adicQuotientAlgebra`、`principalAdicQuotientAlgebra`、`IsGeometricallyTransitive`、`quotientModuleFunctor`、`quotientTensorReductionEquiv`、`quotientScalarExtensionEquiv`、`principalAdicReductionEquiv`。
- 提出候補：`surjective_of_faithfullyFlat_adicReduction`（AdicCompletion/Functoriality の隣）、`subsingleton_of_principal_power_torsion_of_reduction`（中山型）、冪零イデアルでは完全平坦 = 平坦（Tor₁ で書き直して）、冪等元の補題 2 つ、`exists_scalar_inverse_of_ker_coker_annihilated`、`range_rTensor_smul_top`、`finitePresentation_free_quotient_ideal_smul`、`AlgHom.pullback` が CommRingCat の pullback、`Algebra.TensorProduct.mapRingEquiv`、分数体の分離性の移送、不変元のノルム、generic étale。`IsCompletelyFlat` の定義は Mathlib の derived tensor が未整備なので時期尚早。
- リスク：CompletelyFlatCriterion を import する BS 11 本は Andre 系の重いモジュール。`adicQuotientAlgebra` を Mathlib の instance に替えると instance 探索の経路が変わる（`erw`・`change` を使う BS の証明はビルドで確認）。Criterion と Nilpotent の閉包は 62〜67 モジュールなので Basic と分ける。


### 2.8 H perfectoid・完全環・絶対整閉・tilt

規模：75 ファイル、約 6500 行、宣言約 240。BS 25 本・CLMST 33 本の import。

#### 2.8.1 最優先：層の逆転の解消

- CommutativeAlgebra の一部が BhattScholze を import している：PerfectoidIdeal 系（→ `BS.Semiperfectoid.Perfectoidization`）、PerfectoidIdealCompatibleRoots・PerfectoidIdealCover（→ `BS.Semiperfectoid.CompatibleRootPerfectoid`）、AbsolutelyIntegrallyClosedPerfectoidQuotient（→ `BS.Semiperfectoid.Surjectivity`、閉包 71 モジュール）、Perfectoidization（→ `Inputs.Perfectoidization` → BS、閉包 682 モジュール）。
- PerfectoidTorsionQuotient が PerfectoidIdealPowers を import しているため、純可換環論の `IsIntegralPerfectoid.isReduced`・PerfectoidTorsionFrobenius・PerfectoidTorsionTilt まで BS 25 モジュールに依存している。原因は末尾の 1 定理 `perfectoidIdeal_image_p_mul_eq_zero_of_torsionQuotient_perfectoid`（利用者は CLMST/CyclicTorsionComparison だけ）。これを perfectoidIdeal 側へ移せば依存が切れる。他の H の整理と独立に、小さな単独の変更として先に行える。
- BS に依存する層（P8：PerfectoidIdeal・Perfectoidization・PerfectoidizationMap・PerfectoidIdeal{Functor,Powers,Radical,CompatibleRoots,Cover,Pullback}・PerfectoidIdealCompatibility・AbsolutelyIntegrallyClosedPerfectoidQuotient・PerfectoidizationSupportedQuotient）は CommutativeAlgebra の外、BS と CLMST の間の層（例 `SerrePositivity/PerfectoidIdeal/`）へ出す。BhattScholze/ の中へは移せない。BS の `Almost/Lemma103`・`Almost/SupportedQuotient`・`Perfectoidization/Excision` もこれらを import するので、BS 内部の 2 層に挟まる位置になる。
- P1（普遍性）と P8 を同じファイルにすると循環する（BS `Semiperfectoid.Perfectoidization` が CA `PerfectoidizationFunctor` を import し、CA `PerfectoidIdeal` がその BS を import する）。AbsolutelyIntegrallyClosedPerfectoidQuotient も同様。

#### 2.8.2 統合案（`CommutativeAlgebra/Perfectoid/` ほか）

| 新しいファイル | 元のファイル |
| --- | --- |
| Perfectoid/Defs（または Universal） | IntegralPerfectoid・PerfectoidizationUniqueness・PerfectoidizationFunctor・PerfectoidizationIdentity・PerfectoidizationAlgebraMap・PerfectoidizationQuotient・PerfectoidizationNilpotent（Nilpotent は Torsion の後に置く） |
| Perfectoid/Completion | PerfectoidizationCompletion・PerfectoidDerivedComplete（後者は HomologicalAlgebra を import するので別でもよい） |
| Perfectoid/Fontaine | PerfectoidFrobeniusCriterion・PerfectoidCharacteristicP・PerfectionIdempotents・PerfectoidFrobeniusKernel・PerfectoidFontainePrincipal・PerfectoidFontaineSeparation・TiltRootSeparation・WittPrincipalSeparation・CompatibleRootsTilt・CompatibleRootsPerfectoid |
| Perfectoid/Torsion | WittDistinguishedTorsion・PerfectoidPTorsion・PerfectoidRootTorsion・PerfectoidTorsionRoots・PerfectoidReduced・PerfectoidTorsionQuotient・PerfectoidTorsionFrobenius・PerfectoidTorsionTilt・PerfectoidTorsionPerfectoid・PerfectoidUntiltNaturality |
| Perfection | FrobeniusRootKernels・PerfectionPrincipalKernel・PerfectionKernelLift・PerfectionIdealCorrection・PerfectAnnihilator・PerfectionPrincipalQuotientKernel |
| PerfectRing | PerfectPowerReduced・PerfectRadicalIdeal・PerfectCoefficientTensor |
| PerfectPolynomial | PerfectPolynomial・PerfectPolynomialFlat |
| CompatibleRoot | CompatibleRootIdeal・CompatibleRootFamilyIdeal・CompatibleRootIdealFlat・CompatibleRootIdealTensor・CompatibleRootPerfectQuotient |
| AbsolutelyIntegrallyClosed/Basic | AbsolutelyIntegrallyClosed・AbsolutelyIntegrallyClosedFibers |
| AbsolutelyIntegrallyClosed/Etale | AbsolutelyIntegrallyClosedHenselian・Etale・EtaleCover・EtaleAwayCover |

- 外へ回す：FrobeniusHypersurfaceGrowth・FrobeniusKoszulLimit → B2。PowTorsion・PowTorsionCategory・BoundedPowerTorsionQuotient・FlatPowerTorsion・FlatPowerQuotientTorsion → 冪ねじれ・平坦（D）。PerfectNormality → 体論・正規性。PerfectTorIndependence/Basic → HomologicalAlgebra（CA から HomologicalAlgebra への逆依存を解消）。
- Mathlib への置き換え（固定版と最新版に差なし）：`perfect_pow_pow_bijective` → `bijective_iterateFrobenius`。`perfectPrincipalRoot` → `(iterateFrobeniusEquiv k p n).symm a`、`perfectPrincipalRoot_pow` → `iterate_frobeniusEquiv_symm_pow_p_pow`。`surjective_pow_prime_pow` は 2 行。`principalAnnihilator k a` は `(Ideal.span {a}).annihilator`、`pTorsionIdeal` は `Submodule.torsionBy` か同じ零化イデアル（CLMST が使い自ファイル内 56 箇所なので手間が大きい）。`perfectClosure_lift_of` は `symm_apply_apply`。`tiltRootEvaluation` を `((frobeniusEquiv _ p).symm^[n] x).untilt` で定義し直すと `tiltRootEvaluation_pow` は `PreTilt.untilt_iterate_frobeniusEquiv_symm_pow` そのもの。`pTorsionQuotientModPMap` は `modPMap` と定義上同じ。
- 一本化：`isReduced_of_perfectRing_charP` と `isReduced_of_perfectPower`。PerfectoidFrobeniusCriterion の特殊形の入口（N > 1 の一般形へ。BS の PerfectPrismPerfectoid が特殊形を使うので確認）。PerfectoidReduced の特殊化。PerfectoidCharacteristicP の `_of_charP`・`_of_p_eq_zero` の組。互換根の 3 系統（CA `compatibleRootsTilt`・BS `compatibleRootTilt`・`compatibleRoots_pow`・`exists_compatible_pow_roots`）を CompatibleRoot の小さな API に。単項イデアルの零化イデアルの 3 つ。BS の `isIntegralPerfectoid_of_ringEquiv` は本来 IntegralPerfectoid に置くべき補題（BS 側の判断）。
- 未使用：ファイルごと削除できるもの：PerfectoidIdealCompatibility（閉包 682）、AbsolutelyIntegrallyClosedEtaleIntegralCover、PerfectTorIndependence.lean（中身のない入口）。宣言（多くは監査ファイルが名前で参照しているので監査も直す。内部の段は private 化）：AIC の連鎖の中間 3 つと内部専用 5 つ（`henselianLocalRing` は残す）、perfectoidIdeal 系 7 つ、普遍性系 3 つ（`of_completion` は監査 1）、torsion 系 9 つ、Fontaine 系 5 つ（F7 監査の入口）、`bounded_power_torsion_decomposition`、`radicalIdeal_cotangent_subsingleton_of_perfectRing`、`perfection_principal_quotient_zero_branch`。instance `perfectPolynomialAlgebra`・`perfectPolynomialDirectedSystem` はビルドで確認。残すもの：`henselianLocalRing`、`IsAbsolutelyIntegrallyClosed.isAlgClosed`、`perfectPolynomialHomEquiv`、`ker_iterateFrobenius_eq_span`。
- 変えない名前：`IsIntegralPerfectoid`（BS 137 箇所）、`IsPerfectoidization` と `map`・`map_comp`・`map_id`・`map_map`・`lift`、`perfectoidIdeal`、`IsAbsolutelyIntegrallyClosed`、`modPMap`、`untilt_map`、`IsIntegralPerfectoid.isReduced`、`completionLift`・`completionMap`・`isAdicComplete`、`compatibleRootIdeal` 系、`mapAlgHom`、`Perfectoidization`、`coefficientTensorLift`。
- 提出候補：完全環は被約、Perfection の単元判定、完全環上の Witt の単元判定、`Perfection.map` の全射性と核の持ち上げ、完全環のテンソル積の `PerfectRing` instance、冪写像が全射な環の根基イデアルは冪等、分数体の完全性、`ModP` 間の写像と untilt の自然性（Perfectoid/Untilt 向け）、標数 p では ker θ = (p) と生成元の判定（FontaineTheta 向け）、`IsIntegralPerfectoid` の定義と被約性・p ねじれ、`IsAbsolutelyIntegrallyClosed`、`IsAdicComplete` への一意延長の一般化。
- リスク：`IntegralPerfectoid`・`PerfectoidizationFunctor` は BS の大半の祖先で、触ると全面的な再ビルド。P1 の統合は一回にまとめる。監査 audit_clmst・audit_clmst_b3・audit_f6・audit_f7・audit_bhatt_scholze_b5 が宣言名を参照（private 化すると `#print axioms` の対象から消える）。BS セッションの区切りに合わせて行う。


### 2.9 X どの群にも入っていなかった残り

規模：52 ファイル、約 5500 行（単独 28 本、RootTower/ 18 本、Almost/ 6 本）。

| 小群 | 新しいファイル | 元のファイル |
| --- | --- | --- |
| CubicCyclotomic | Algebra | CubicCyclotomicAlgebra・CubicCyclotomicFiber |
|  | LocalExtension | CubicCyclotomicClosedPoint の生きている部分・CoprimeFactorLocalization・LocalizedSurjectiveQuotient・CubicCyclotomicClosedFiber・CubicCyclotomicLocalFiber・CubicCyclotomicLocalExtension（互いに鎖状に import するので一緒に） |
| RootTower | Basic・MonomialBasis・Stage はそのまま | |
|  | Completion | Completion・CompletionFlat・Restriction |
|  | CompletedRoots | CompletedRoots・CompletedRepresentatives |
|  | ModP | ModPFrobenius・ModPInjectivity・ModPSurjectivity・ModPEquiv・ModPComparisonLength |
|  | Perfectoid | CompletedTilt・CompletedFrobenius・FrobeniusKernel・WittPresentation（CompletedRoots と分けるのは H・Witt の import を CLMST に持ち込まないため） |
|  | Koszul | そのまま（重い。利用者は Paper/Section2/CompletedTower だけなので Paper へ移す案も） |
| Almost | Basic | Zero・Morphism |
|  | Category | Category・TorsionCategory・SerreComparison |
|  | Quotient | そのまま（BS が import） |
| Support | Closed | ClosedSupportGeometry・PrincipalSupport・ModuleClosedSupport（B2 の台の補題・SupportHeight も寄せる案。ClosedSupportGeometry は InfinityCategories・KTheory に広く import されるので、統合先の名前を既存のまま残す手もある） |
| ReducedSpectrum | ReducedSpectrum | FiniteSpectrumPartition・ReducedPrincipalVanishing・ReducedSectionImage（D の IdempotentAnnihilator・ProductIdempotentQuotient と同居の候補） |

- 他の群へ：ConductorQuotient・TraceConductor（`Conductor.lean`）・GaloisNormalization → Paper 層。AlgebraMapCokernel → B。PrincipalMaximalFactorization・RootTower/Restriction の `maximalIdeal_map_le_of_finite_of_injective` → C。LocalResidueLinearMap・MappedPrincipalQuotient → D（後者は PrincipalAdicReduction と同居）。PrincipalAlgebraIsomorphismLocus → E（FiniteAlgebraLift と）。PrincipalQuotientAnnihilator → H。CoefficientTensorAutomorphism → PerfectCoefficientTensor の隣。DerivedSingleTrianglePullback・MinimalGenerators → HomologicalAlgebra。FractionRingBasis → FieldTheory か SeparableBaseChange と。SubmoduleExact → KTheory か LinearAlgebra。
- 削除してその場に書く：QuotientBaseChange（`quotientBaseChangeEquiv` は Mathlib の `TensorProduct.tensorQuotMapSMulEquivTensorQuot` と型が同じ。利用は FlatLocalDimension の 1 か所）、AlgebraAction（`MulSemiringAction.toAlgAut` と `AlgHom.comp_algebraMap` から出る。利用 3 本）。
- Mathlib：GaloisNormalization の `isSeparable_normalClosure` は最新版の instance `IntermediateField.normalClosure.isSeparable` で、Mathlib を上げたら削除。`cubicCyclotomicPolynomial` を `Polynomial.cyclotomic 3 R` の abbrev に（約 30 参照）。MinimalGenerators の `rank` → `spanFinrank`（`TensorProduct.spanFinrank_top_eq_of_residueField`）、`π_surjective` → `IsLocalRing.span_eq_top_of_tmul_eq_basis`。`quotientSmulCokerEquiv` → `DoubleQuot.quotQuotEquivQuotSup` と `quotEquivOfEq`。AlgebraMapCokernel は中身だけ簡単に（CLMST が使うので名前は残す）。
- 一般化：CubicCyclotomic の局所拡大は「monic な f と剰余体での互いに素な分解 f̄ = g·h（g 既約）」だけを使っているので、一般の局所拡大として書き、「3 が単元」の部分だけを特殊に残す。`principalSupport_add` は閉台の族一般の補題。ConductorQuotient と TraceConductor は「共通分母 g で gC ⊆ B」という一つの話。
- 未使用：CubicCyclotomic 系 13 前後（ClosedPoint はファイルの大半が死んでいる）、RootTower 系 8 前後（CompletedTilt の死んだ枝など。audit/shared の assertion も削除）、TraceConductor・ReducedSectionImage・MappedPrincipalQuotient の各 1、Almost 系 6 前後（`IsAlmostZero.bot` などはドット記法での利用を個別に確認）。
- 変えない名前：RootTower の名前空間 `SerrePositivity.Section2`（CLMST で `CompletedTower` 754 箇所、`TowerStage` 181 箇所）。
- 提出候補：LocalResidueLinearMap（剰余体でのテンソルが全単射なら全単射）、整域を仮定しない主極大イデアルの分解、`AdjoinRoot.map_mk`・`map_surjective`、FiniteSpectrumPartition・ReducedPrincipalVanishing、SubmoduleExact、RootTower/MonomialBasis、CoefficientTensorAutomorphism、ConductorQuotient。
- リスク：RootTower/Stage・Completion・CompletionFlat は CLMST の大部分の上流にあり、触ると CLMST 全体が再ビルド。ファイル統合だけで CLMST 約 12 本の import 行が変わる。

- 決定（2026-10-30、ユーザー、X の軽い小群）：
  (1) CubicCyclotomic の局所拡大を「monic な f と剰余体での互いに素な分解 f̄ = g·h（g 既約）による局所拡大」の一般論に書き直す。
  三次円分に固有の部分（3 が単元）だけを特殊に残す。IntersectionMultiplicity・PerfectComplex の約 30 参照への波及も合わせて直す。
  (2) `cubicCyclotomicPolynomial` を `Polynomial.cyclotomic 3 R` の abbrev にする。
  (3) Support の統合先は新しい `Support/Closed`（ClosedSupportGeometry の名前は残さない。InfinityCategories・KTheory の import 行を
  書き換え、その範囲の再ビルドを伴う）。
  (4) CommutativeAlgebra/Almost と LengthAlgebra/Almost* を一つの群として整理する（置き場所はその作業で決める）。
  (5) BhattScholze が import する DerivedSingleTrianglePullback・MappedPrincipalQuotient・CoefficientTensorAutomorphism の移動は、
  BhattScholze 側を再ビルドする別の作業に回す（Koszul・KoszulResolution の移動と同じ扱い）。


### 2.10 章の中の作業順

（全体の順序は E が正本。B1・B2・C3 は完了。）残りは区切り 1-1 の中で X の軽い小群 → E → D → H の BS に依存しない部分の順に行い、
H の BS 依存部分と RootTower の BS 側は区切り 2a で行う。群をまたぐ共通の置き換え（`stableFiltration`・`fwdDiff`・`reduceModIdeal`・
`Module.IsTorsion'`・`LocalizedModule.map`・Frobenius の反復 API）は、それぞれ該当する群の中で行う。

## 第3章 HomologicalAlgebra

### 3.1 群の分け方と外への影響

| 群 | 内容 | ファイル数 | 行 | BS が直接 import するファイル |
| --- | --- | --- | --- | --- |
| HA1 | 複体の基礎：Cochain*・テンソル・錐・切り詰め・冪等元・BoundedAbove・分解・線形 Yoneda・列の余極限 | 136 | 約 14000 | 少数（BoundedAboveDerivedAssociator・BaseChange、KProjectiveLift、RestrictedBaseChangeScalar、CompatibleRootQuotientTor、SequentialComplexColimits） |
| HA2 | 導来テンソル・導来代数・H⁰ の環・純な導来 Cartier・導来平坦性 | 105 | 約 12500 | 約 20 |
| HA3 | Koszul・Tor・局所コホモロジー・基底変換・有限自由分解・Auslander–Buchsbaum | 118 | 約 12500 | 約 18 |
| HA4 | DerivedCompletion の塔の側：Tower・Milnor・Koszul 塔・Principal・Pair・Power・Restriction・IteratedTensor | 88 | 約 9500 | 約 20 |
| HA5 | DerivedCompletion の完備化の側：Module 完備・ComplexCompletion・BoundedAbove 完備化・完備テンソル・完備代数の H⁰・ModulePower | 104 | 約 10000 | 31 |

- BS が多く使う名前：`IsModuleComplete`（BS 35 ファイル・CLMST 14）、`PDCompletionH0`・`pdCompletionUnit`・`pdCompletionCommRing`（BS 33）、
  `boundedAboveDerivedBaseChange`（BS で 557 回）、`boundedAboveDerivedCompletionFunctor`（BS 18）、`derivedComplexCompletionFunctor`（BS 13・CLMST 9）、
  `PrincipalCompletionH0`（29 回）、`principalCompletionCommRing`（22 回）、`pairKoszulCoordinates`（16 回）。これらは名前を変えない。
- PerfectComplex にも CochainTensor 系がある（第4章）。本体は HA に置く（§3.8 の 3）。

### 3.2 HA1 複体の基礎（136 → 約 20 ファイル）

#### 3.2.1 統合

| 新しいファイル | 元のファイル |
| --- | --- |
| Complex/Basic | Basic・CochainBiproduct・CochainKernelLift・CochainTwoTermScalarMap（ProjectiveBaseChange は削除） |
| Complex/Cone | CochainConeArrowMap・ConeCoordinates・ConeNaturality・ConeAdditiveNaturality・ConeProduct・ConeTriangle（Mathlib の MappingCone だけ） |
| Complex/ConeLES | ConeLES・CochainAcyclic（ConeLES は importer 16 本なので軽く保つ） |
| Complex/Truncation | StupidTruncation・TruncationBoundary・NullHomotopy |
| Complex/Idempotent | CochainIdempotent と Acyclic・Decomposition・Sum・FiniteSum・Functor・Homology・Iso・QuasiIso・ShortExact・Trivial（約 780 行） |
| Tensor/Basic | CochainTensor と Linear・DegreeMaps・Bounds・Finite・Projective・Symmetry・Homotopy・Shift、CochainIdempotentTensor |
| Tensor/Coherence | Shuffle・Homogeneous・Triple・TripleDifferential・TripleDegreeMaps・Hexagon・Braided・ShuffleEquivariance・ScalarCoordinates・Six*（約 1100 行、Triple と Six に分けてもよい） |
| Tensor/Exactness | ShortExact・TripleShortExact・Single・Cone・Acyclic・BoundedAbove |
| Tensor/BaseChange | CochainTensorBaseChange・BaseChangeSymmetry・TripleBaseChange・BaseChangeSingle・RestrictedBaseChangeComplex（RestrictedBaseChangeScalar は重いので別） |
| Tensor/SingleMonoidal | CochainSingleTensorComparison・CochainSingleMonoidal・CochainDiscreteAlgebra（MonoidalUnitHomRing・MonoidalPointAction は圏論なので HA の外へ） |
| Tensor/ScalarCone | CochainTensorScalarCone・LinearFunctorScalarCone（Koszul を import するので軽いファイルに混ぜない） |
| KProjective | KProjectiveLift・KProjectiveCohomologyLinear |
| BoundedAbove/Derived | ProjectiveResolution・ResolutionFunctor・DerivedModels・LeftDerived・DerivedAdditive・DerivedShift・DerivedCone・DerivedConeTriangle・SourceConeTriangle（ExactDerived は任意） |
| BoundedAbove/Tensor | TensorModels・TensorFunctor・DerivedTensor・DerivedAssociator・DerivedUnit・DerivedBaseChange（DerivedModule・DerivedAcyclic・DerivedTruncation は重い層を引くので別のまま） |
| Resolution | Resolution・ResolutionNaturality・ResolutionMappingCone・ConeResolution・BoundedResolutionDimension |
| LinearYoneda | ChainLinearYoneda・InjectiveLinearYoneda・ProjectiveLinearCoyoneda・ChainLinearYonedaZero・ProjectiveExtNaturality・ProjectiveResolutionInjectiveAcyclic・CochainLinearDual・MappingConeLinearDual・CochainLinearDualCone |
| ComplexColimits | SequentialComplexColimits・ExactChainHomologyColimits・ExactFunctorColimits・LinearFunctorColimits |
| Ext/LocalCohomology | ProjectiveExtSequence・ProjectiveExtColimitExact・InjectiveCoefficientDimensionShift・GeneralKoszulLocalCohomology・GeneralLocalCohomologyBaseChange |
| MinimalResolution | MinimalFreeResolution・MinimalBetti・MinimalTruncation・MinimalBoundary |
| ScalarConeAnnihilators | TwoTermConeAnnihilator・ConeComparisonSquare・ConeOfSurjectiveSource・ConeFiniteCover・TwoCohomologyAnnihilator（後ろの 2 本は重いので層の最後で） |

- 他の群へ回す：CompatibleRoot{Family,FiniteFamily,Quotient}Tor → HA3 の Tor。ModelTensorFlatCriterion・ModelTensorHomologySurjective → HA2 の導来平坦性。
  BoundedKoszulAugmentation・BoundedTermKoszulAcyclic → HA3 の Koszul。ChainAugmentationNormalization・CochainAugmentationModels → HA2 の augmentation。
- 層の逆転（∞ 基盤の側へ渡した、伝達文 §5）：`ComplexLimits/*`（3 本）は KST.LocalizingInvariants を import し、名前空間は `SerrePositivity.EInfinity.ComplexLimits`。
  `EInfinity/ComplexLimits/*` は再エクスポートの殻だけ。1 本にまとめて EInfinity 側へ移し、殻を消す。
- Basic.lean が `HomotopyCategory.MappingCone` と `Noetherian` を import していて、importer 15 本に重さを渡している。Resolution.lean の
  `Mathlib.Data.Real.Basic`・`Mathlib.Tactic.Ring` も不要に見える。統合のときに import を絞る。

#### 3.2.2 Mathlib との重なり

- StupidTruncation の `above`・`below`・`inclusion`・`projection`・`inclusion_f_isIso`・`projection_f_isIso` → `HomologicalComplex.stupidTrunc`・
  `ιStupidTrunc`・`πStupidTrunc`・`isIso_ιStupidTrunc_f`・`ιStupidTruncNatTrans`（確度高）。**最新版にしかない**（固定版は `stupidTrunc` だけ）。
  **決定（2026-10-30）**：Mathlib を上げるまで保留。
- `ProjectiveBaseChange.projective_baseChange` は `infer_instance`（削除）。`CochainBiproduct` の instance は `HasFiniteBiproducts.of_hasFiniteProducts`。
  `CochainIdempotentQuasiIso.imageMap_quasiIso` は `quasiIso_of_retractArrow` の 1 行の包み。
- KProjective の持ち上げ 3 本（`BoundedAboveDerivedModels.exists_cochainMap_of_isKProjective`、`KProjectiveLift.exists_lift_of_quasiIso`、
  `homotopyOfDerivedMapEq`）は `IsKProjective.Qh_map_bijective`＋`quotientCompQhIso` の同じ議論。1 本にする。
  `kProjectiveCohomologyDerivedEquiv` は `CohomologyClass.equivOfIsKProjective` と `SmallShiftedHom.equiv` の合成（確度中）。
- `linearYonedaModule_preservesHomology` 系 → `preservesHomology_preadditiveYonedaObj_of_injective` 系（確度中。Mathlib は AddCommGrp 値）。
- `isZero_homology_of_isZero_X` → `ShortComplex.isZero_homology_of_isZero_X₂`、`projective_of_free` → `ModuleCat.projective_of_free`、
  `isZero_moduleCat_free` → `Module.Free.of_subsingleton`（いずれも確度中）。
- テンソル積（訂正）：`cochainTensor` などは Mathlib の `HomologicalComplex` のモノイダル構造（Algebra/Homology/Monoidal.lean）の薄い包み
  （`cochainTensor` = `tensorObj`、`cochainTensorMap` = `⊗ₘ`、`cochainTensorAssociator` = `α_`、`cochainTensorShuffle` = `tensorμ` など、確度高）。
  詳しくは §4.3.2。Mathlib にないのは Koszul 符号付きの組みひも（`β_`）と
  `(tensor C).Braided`。
- Mathlib にないもの：複体の Koszul 符号付きの組みひも（Symmetry・Hexagon・Braided）、`MonoidalLinear`、`single₀` のモノイダル性、
  `restrictionFunctor`・`extendFunctor` の `Linear`、exact colimit と homology の可換、`Resolution.leftDerived_additive`、`DerivedCategory.Minus` 上の
  左導来関手（Mathlib の TODO にある）。

#### 3.2.3 一本化

- SequentialChainHomologyColimits は ExactChainHomologyColimits の `J = ℕ` の写し。削除。
- ConeResolution の `coneHomologyZeroEquiv`・`isResolutionOf_cone` は ResolutionMappingCone の特殊化。
- `BoundedAboveDerivedModel` と `BoundedAboveProjectiveResolution` は `map`・`mapIdHomotopy`・`mapCompHomotopy`・`map_quasiIso` が並行。
- DegreeMaps と TripleDegreeMaps、Shuffle と SixShuffle は項数違いの同じ API。一般化は後回しでよい（記録だけ）。
- `TruncationBoundary.boundary` と `MinimalBoundary.boundary` は特殊化の関係で、名前空間違いの同名。

#### 3.2.4 未使用

- BoundedAbove：`boundedAboveDerivedTensor{Associator,LeftUnitor,RightUnitor}NatIso`、`boundedAboveLeftDerived{Cone,}Triangle_homology_exact`、
  `boundedAboveLeftDerivedShiftNatIso`、`boundedAboveDerivedTensorComplexComparison`、`boundedAboveResolutionFunctor`、
  `boundedAboveDerivedTensorFunctor_map_isIso`、`boundedAboveDerivedTensorAugmentation`、`derivedTensorComparisonIso_augmentation`。
- 冪等元：`imageMap_id/_comp`、`ι_decompositionIso_hom`、`decompositionIso_inv_π`、`imageFiniteSumIso_hom_inclusion`、`imageFunctorIso_naturality`、
  `image_{finite,projective,isZero}_X`、`imageIsoOfMapEqId_hom/_inv` ほか。
- テンソル：`cochainSingleTensorIso_naturality`、`cochainTensor_d_comp_d`、`extendScalars_braiding_delta`、`cochainTensorSummand_isZero_right`、
  `tensorConeInlX_fst/_snd`、`cochainTensorConeTriangleIso`、`exists_cochainTensorX_finiteCoproductModel`、`cochainTensor_isZero_X_of_bounds`、
  `cochainTensorFixed{Right,Left}_commShift` ほか。
- 線形双対：`cochainLinearDualNonnegativeNatIso_complex_map`、`cochainLinearDualTermIso`、`cochainLinearDual_map_apply`、
  `mappingConeTargetHomEquiv_d_snd`、`scalarMappingConeTargetHomEquiv_d_fst` ほか。
- その他：`chainHomologyZeroProjection_descOpcycles`、`mono_homologyMap_liftSES_zero`、`generalKoszulLocalCohomologyComparison_map_eq_zero_iff`、
  `injectiveCoefficientHomologyNatIso_zero/_unique`、`chainLinearYonedaObjIsoMapOp`、`MinimalBetti.finrank_eq_length_tor`。
- instance と `@[simp]` は暗黙に使われうるので、削除の前にビルドで確かめる。HA の中に importer がないファイル（CochainIdempotent の一部、
  CochainTensor の Triple*・ShuffleEquivariance など、MinimalBoundary）は外の利用者を確かめる。

#### 3.2.5 選択と構成

- `BoundedAboveProjectiveResolution.ofBoundedAbove`・`BoundedAboveDerivedModel.ofIsLE` は `Classical.choice`、`comparison`・`map`・`mapHomotopy` は
  存在定理の `.choose`。`IsKProjective` の持ち上げ（Mathlib の `equivOfIsKProjective`）から直接作る。BS が使う名前は残す。

#### 3.2.6 提出候補

複体の対称モノイダル構造（`HomologicalComplex C c` へ一般化して）、`MonoidalPreadditive`・`MonoidalLinear`、`single₀` のモノイダル性、
`restrictionFunctor`・`extendFunctor` の `Linear`、exact colimit と homology の可換、関手の複体への転置、`QuasiIso f ↔ (mappingCone f).Acyclic`
（アーベル圏へ一般化して）、冪等鎖写像の像と分解、`Resolution.leftDerived_additive`、「homology が r で消える有界複体では r の冪が零ホモトピック」。

### 3.3 HA2 導来テンソル・導来代数（105 → 約 18 ファイル）

#### 3.3.1 統合（import の順）

| 新しいファイル | 元のファイル |
| --- | --- |
| DerivedHomologyBasics | DerivedPureHomology・DerivedHomologyLinear（Mathlib だけ） |
| DerivedRestriction | DerivedRestriction・DerivedRestrictionConservative・AlgebraRestrictionSingle・AlgebraScalarExtensionModule、RingEquivDerivedTensor の `derivedRestrictScalars_isGE_iff/_isLE_iff` |
| ClassicalDerivedTensor | DerivedTensor・DerivedTensorRealization・DerivedTensorModuleResolution・DerivedTensorBaseChange・ScalarExtensionTensorCancellation |
| UnitHomology | UnitLinearHomComplex・DerivedUnitHomology・UnitHomologyNaturality・DerivedUnitHomologyNatural |
| TensorComplexNaturality | TensorBaseChangeNaturality・TensorConeNaturality・TensorSingleNaturality |
| DerivedTensorMonoidal | DerivedTensorCoherenceModels・Triangle・Pentagon・Monoidal・Symmetry・Braided・Linear（一本の鎖） |
| DerivedTensorModules | DerivedBaseChangeTensor・DerivedTensorModuleModels・ModuleComparison・TorNaturality・UnresolvedModule・DerivedNonpositiveHom・DerivedTensorNonpositive・ModuleNaturality・DerivedFlatModelTensor |
| DerivedTensorAugmentation | DerivedTensorAugmentationModels・DerivedBaseChangeAugmentationModels・…Comparison・DerivedBaseChangeTensorAugmentation・AlgebraBaseChangeTensorAugmentation・DerivedTensorFixedModuleModel |
| DerivedAlgebraObjects | DerivedDiscreteAlgebraMaps・DerivedSingleTensorSymmetry・DerivedSingleTensorUnit・DerivedAlgebraAssociativity・DerivedAlgebraObjects・DerivedAlgebraMorphisms・DerivedTensorAlgebraAugmentation |
| DerivedH0Ring | DerivedH0Algebra・UnitHomologyNormalization・DerivedSingleH0Algebra・DerivedTensorH0Algebra・DerivedTensorH0Coefficient・DerivedDiscretePointAction・DerivedRestrictionNormalization・DerivedRestrictionSingleH0・AlgebraBaseChangeTensorH0 |
| DerivedTensorCompletionAlgebra | DerivedTensorAugmentationIso・DerivedTensorAlgebraCongruence・RingEquivDerivedTensor（DerivedCompletion を import するので DerivedH0Ring と分ける） |
| DerivedQuotientBaseChange | DerivedBaseChangeDiscrete・DerivedQuotientBaseChange・DerivedBaseChangeRightTensor・DerivedQuotientH0Normalization・DerivedQuotientTensorAugmentation・QuotientSupTorComparison |
| DerivedKoszulCones | DerivedModuleCone・ScalarConeModuleQuotient・DerivedQuotientKoszul・DerivedKoszulDescent・DerivedScalarConeBaseChange・DerivedTensorKoszul・ScalarConeShiftNaturality |
| PureDerivedCartier | PureDerivedCartier{Quotient,Naturality,Single,Representatives,ModuleRepresentatives}・DerivedTensorPureFactorization・DerivedTensorCartierProducts |
| DerivedFlatness | DerivedAcyclicSingle・DerivedAcyclicHomology・NilpotentDerivedReduction・ScalarExtensionTensorTests・FlatDerivedPowerReductions（CompletedFlat* 3 本は DerivedCompletion を引くので別ファイル） |
| AlgebraKoszulDual | AlgebraLinearYoneda・…BaseChange・AlgebraMappingConeDual・AlgebraKoszul{Dual,Colimit,Bounds,Augmentation,AugmentationZero,TermColimit}・AlgebraEquivariantShortComplex |
| FlatKoszul | FlatBaseChange・FlatKoszulFiniteness（CLMST が使う） |
| ModuleTorsion | IdealPowerTorsion・IdealPowerTorsionSupport・IdealPowerTorsionBaseChange・NilpotentModuleFiltration・ScalarWeightedColimit・QuotientTorOneConormal |

- DerivedRestrictionNormalization・DerivedRestrictionSingleH0 は UnitHomologyNormalization 経由で DerivedTensorBraided を引くので DerivedRestriction に入れない。
- `koszulModuleFunctor_self_eq` は FlatKoszulFiniteness にあるが一般の Koszul の補題（HA3 へ）。
- `maxHeartbeats` を上げているファイル：DerivedQuotientTensorAugmentation・PureDerivedCartierNaturality（800000）、DerivedTensorPentagon（600000）。
  統合のときは節ごとに `set_option … in` にする。

#### 3.3.2 Mathlib との重なり

- 導来テンソル、`DerivedCategory` のモノイダル構造はどちらの版にもない。DerivedTensorMonoidal 以下は置き換えられない。
- `derivedTensor` は `((tensoringLeft _).obj M).leftDerivedToHomotopyCategory.obj N` の薄い包みで、`derivedTensor_homology_eq` は Mathlib の
  `Tor`（Monoidal/Tor）の定義そのもの（確度高）。
- `derivedRestrictScalars`・`…Factors`・`…SingleIso` は `Functor.mapDerivedCategory`・`mapDerivedCategoryFactors`・`mapDerivedCategorySingleFunctor`
  の 1 行の別名（確度高。BS が名前を使うので残し、定義を `abbrev` に）。
- `flat_of_algebra_isPushout` → `Module.Flat.isBaseChange` 系（確度中〜高、CLMST が使う）。`scalarExtensionTensorCancelIso` は
  `AlgebraTensorModule.cancelBaseChange` の圏論的な包み（確度中）。

#### 3.3.3 一本化

- **導来テンソルが 3 通り**：`derivedTensor`（ℕ ホモトピー圏）、`realizedDerivedTensor`、`boundedAboveDerivedTensor`。比較のためだけのファイル
  （DerivedTensorModuleComparison・DerivedTensorFixedModuleModel）がある。長期には `boundedAboveDerivedTensor` に寄せる。前の 2 つは BS が名前を
  使う（`derivedTensor`・`IsConcentratedInDegreeZero`・`realizedSingleH0Iso`）ので、すぐには消さない。`realizedDerivedTensorHomologyIso` と
  `derivedTensor_homology_eq` は Tor の同定の言い直しで、ファイルの外で使われていない。
- DerivedUnitHomology の `derivedUnitHomologyLinearEquiv`・`derivedUnitH0HomLinearEquiv` は Natural 版と重複。Natural 版だけ残す。
- `derivedModuleBaseChange*`（DerivedTensorBaseChange）と `boundedAboveDerivedBaseChangeModule*`（HA1 の BoundedAboveDerivedModule）が並行。両方 BS が使う。
- H⁰ の正規化が 4 系統（UnitHomologyNormalization、DerivedRestrictionNormalization＋SingleH0、DerivedQuotientH0Normalization、HA3 の
  RealizedSingleH0Normalization）。共通の補題で書けるか、統合のときに確かめる。

#### 3.3.4 未使用（全 105 ファイルを名前で走査。instance と `@[simp]` は除く）

`algebraKoszulDualColimitAugmentation_ι`、`parameterKoszulColimitAugmentation`、`algebraKoszulDualIntegerLocalCohomologyComparison`、
`parameterKoszulColimit_isZero_X_above/_below`、`boundedAboveDerivedAlgebra_mul/_one`、`boundedAboveDerivedTensorAlgebra_X`、
`boundedAboveDerivedTensorBaseChangeModuleIso_naturality`、`restrictedDerivedTensorBaseChangeRightNatIso`、`derivedH0AlgMap_id`、
`derivedKoszulHomology_uniform_annihilated_iff`、`derivedKoszul_homologyTorAcyclic`、`moduleMapConeScalar_eq_zero_annihilates_ker`、
`derivedTensorQuotientModuleIso_naturality`、`boundedAboveDerivedAlgebraIso`、`boundedAboveCompletedTensorAlgebraIso_left/_right`、
`realizedDerivedTensorH0Iso`、`realizedDerivedTensor_discrete_iff`、`primaryComponent_eq_of_radical_eq`、`pureDerivedAlgebraCartierQuotient_pure`、
`completedTensorModulesRingEquivRestriction_homology_isZero_iff` ほか（調査メモの全リストを作業時に再確認する）。

#### 3.3.5 選択と構成

- `normalizedPureHomologyIso := (exists_normalizedPureHomologyIso X i).choose`（BS・CLMST が使う）。一意性は証明済みなので標準的だが、展開できない。
  t 構造の切り詰めから直接作るか、このまま残すかを決める。
- `quotientTorOneConormalEquiv` は `Classical.choice (nonempty_torModule_one_equiv_ker …)` で作られ、同型が標準的でない（BS が使う）。
  連結写像から構成的に作り直す。Mathlib に出すならこれが前提。

#### 3.3.6 提出候補

`DerivedCategory.homologyFunctor` の `Linear`、純な対象と `singleFunctor` の標準同型（DerivedPureHomology）、`Ideal` の冪ねじれ関手と根基への
非依存性、`Hom(R/I, M) ≃ₗ torsionBySet M I`、`Tor₁(R/I, R/I) ≅ I/I²`（構成的にしてから）、冪零フィルトレーションの補題、`derivedRestrictScalars`
が同型を反映すること。`DerivedCategory.Minus (ModuleCat R)` のモノイダル構造は価値が高いが大仕事。

### 3.4 HA3 Koszul・Tor・局所コホモロジー（118 → 約 20 ファイル）

#### 3.4.1 統合（import の順）

| 新しいファイル | 元のファイル |
| --- | --- |
| ModuleBaseChange | BaseChange・ModuleBaseChangeTensor・ModuleScalarExtensionAnnihilator・FiniteFreeBaseChange |
| ModuleCatColimits | ColimitLinearFunctor・FiniteSupportCoproduct・FiniteSupQuotientColimit |
| Tor/Basic | Tor・TorUniformAnnihilator・BaseChangeEquivalence（BaseChange は importer 12 本なので Tor に入れない） |
| Tor/LongExact | TorLES・TorNaturality・TorSymmetry・LeftDerivedZeroFunctorNaturality・CoefficientDimensionShift |
| Tor/Flatness | LocalFlatnessCriterion・TorDimensionShift・TorFlatBaseChangeVanishing・TorBaseChange（`torModule_subsingleton_*` の一般の補題は Tor/Basic へ） |
| Tor/Length | TorFiniteLength・TorFiniteLengthBound・TorTwoRingComparison・KoszulTorLength・KoszulOrdinaryLength |
| Koszul/CoefficientFunctor | DirectedHomology・KoszulDirectedLimit・KoszulScalarControl・KoszulCoordinateControl・KoszulModuleBounds・KoszulIdealAction・KoszulRadicalSupport・KoszulRestriction・KoszulOneCoordinates・KoszulWeightedColimit |
| Koszul/Towers | KoszulTower・KoszulTruncation・KoszulDirectedUnion・HomologyQuotient |
| Koszul/TorComparison | KoszulTorComparison・KoszulTensorConeComparison・KoszulAlgebraTorComparison・TorCoefficientIdeal・TorAlgebraScalarComparison・TorAlgebraNaturality |
| Koszul/ParameterAnnihilators | KoszulHomologyAnnihilator・ParameterKoszulComparison・ParameterKoszulIdempotent・FiniteParameterKoszulAnnihilator・TorFiniteFreeComparisonAnnihilator・TorAlmostComparisonTransport |
| Tor/Colimits | TorSequentialColimits・TorExactColimits・TorFiniteCoefficients・BalancedTorResolution・ModuleTensorChainFunctor |
| Tor/AcyclicBaseChange | TorAcyclicBaseChangeResolution・…Comparison・TorAlgebraAcyclicBaseChange・FiniteCohomologyBaseChange・PrincipalQuotientResolution・RegularPrincipalTor・PowerTorsionTorBaseChange |
| Tor/FlatDescent | FaithfullyFlatDerivedHomology・PowerTorsionDerivedDescent・TorCoefficientPowerTorsionDescent・PowerTorsionCompletedBaseChange・CompleteTwoCohomologyAnnihilator・CompleteFaithfullyFlatDescent |
| Tor/PerfectRings | PerfectRadicalQuotientTor・PerfectRingTor・PerfectResidueTensorRegular |
| Koszul/LinearDuality | KoszulLinearDuality・…Naturality・NonnegativeCochainHomology・HomComplexCone・KoszulBaseChangeNaturality |
| LocalCohomology/KoszulComparison | ExtZeroComparison・KoszulExtComparison・LocalCohomologyKoszulPowers・…Comparison・KoszulDualZero・…Transitions・…Torsion・KoszulDualCoefficientExact・KoszulDualInjectiveAcyclic・ArtinReesHomology・KoszulTransitionDepth・KoszulDualBaseChange |
| LocalCohomology/Actions | KoszulDualTorComparison・LocalCohomologyAction・KoszulLocalCohomologyAction・LocalCohomologyScalarBaseChange・LocalCohomologyTorAnnihilator・ParameterLocalCohomologyAnnihilator・LocalCohomologyZeroTorsion |
| Resolution/FiniteFree | FiniteFreeResolution・RegularLocalResolution・LocalizedRegularResolution・FiniteLocalizationDescent・FiniteResolutionTrace・ControlledHorseshoe・ControlledResolution |
| AuslanderBuchsbaum | AuslanderBuchsbaum・RegularQuotientProjectiveDimension（§3.4.2） |
| ComplexUtilities | ModuleSubcomplex・AdicFilteredComplex・UniformNullHomotopy・SupportNullHomotopy・MapExtend・CoaugmentedReflection・ModuleTensorCochain{Filtration,Exact}（軽い側）と SingleTriangleExactReflection・RealizedSingleH0Normalization（導来圏側）に分ける |

- 循環の危険：KoszulDualTorComparison は KoszulExtComparison を import し、KoszulDualBaseChange は KoszulBaseChangeNaturality を import する。
  Koszul/LinearDuality → LocalCohomology/KoszulComparison → LocalCohomology/Actions の順を守る。
- `torCoefficientScalarEndomorphism`（BS・CLMST が使う Tor の係数作用）は KoszulTorComparison にある。Tor/Basic か Tor/LongExact へ移す（名前は残す）。
- 死んだファイル：KoszulHomologyLength（LengthAlgebra の再エクスポートのみ）、LocalCohomologyZeroBaseChange、PerfectQuotientTorOne、
  PowerResidueDerivedHomology（どれも importer は `SerrePositivity.lean` だけ）。
- HA1 から CompatibleRoot*Tor・BoundedKoszul* を受け入れる。HA4 の PowerTorsionTor* も Tor 側が自然（§3.5.1）。

#### 3.4.2 Mathlib との重なり

- Koszul 複体、Auslander–Buchsbaum、左導来関手の長完全列、加群の Tor の包み、Tor の対称性は、どちらの版にもない。
- `free_baseChange`・`finite_baseChange` は `infer_instance` の包み（確度高、インライン化）。
- `ModuleCat.free_of_projective_of_isLocalRing` → `Module.free_of_flat_of_isLocalRing`（確度高）。
- `torModule_free_succ_eq_zero`・`torModule_pi_self_subsingleton` → `isZero_Tor_succ_of_projective` の 1 行の系（確度高）。
- AuslanderBuchsbaum・RegularQuotientProjectiveDimension は Mathlib の PR（commit 9c971a55）からの写しで、どちらの版にもまだない。
  主定理 `auslanderBuchsbaum` も `projectiveDimension_eq_regularQuotient` も未使用。名前に typo（`finte_free_ext_vanish_iff`）、
  ルート名前空間の一般の補題（`smul_prod_of_smul`・`subsingleton_of_pi`・`basis_lift` など）、`AuslanderBuchsbaum`/`auslanderBuchsbaum` の大小違いの対がある。
  **決定（2026-10-30）**：削除する（AuslanderBuchsbaum・RegularQuotientProjectiveDimension のファイルごと。利用者がないことを作業時に再確認）。
- `flat_of_torModule_one_residueField` は A = B・有限表示なら `Module.free_of_lTensor_residueField_injective` 系で足りる。A→B の一般形は Mathlib にない（確度中）。
- ExtZeroComparison は `Ext.homEquiv₀`・`Ext.linearEquiv₀` と重なる（確度中）。DirectedHomology は `ModuleCat.AB` の filtered colimit の完全性から出せる見込み（確度中）。

#### 3.4.3 一本化

- `moduleCatBaseChangeTensorEquiv`（ModuleBaseChangeTensor）≡ `extendScalarsObjEquivTensor`（TorBaseChange、BS が使う）。後者を残す。
- `torModule_smul_eq_zero` ≈ `Tor.annihilator_le_torModule_right`。`torModule_one_subsingleton_of_exact` は `torModule_subsingleton_of_exact` の n = 1。
  `torModule_subsingleton_of_linearEquiv` ≈ `Tor.torAlgCongr`。PerfectQuotientTorOne は PerfectRadicalQuotientTor の i = 1。
  `length_homology_koszul_equiv` は `length_homology_baseChange_equiv` の特殊化。
- Koszul と Tor の比較が 3 系統（KoszulTorComparison・KoszulTensorConeComparison・KoszulAlgebraTorComparison）。それぞれの `_scalar_eq_zero_iff`・
  `_of_tor_annihilated`・`*PowersComparison` の多くは未使用。
- 忠実平坦の降下の骨組みが 3 回（FaithfullyFlatDerivedHomology・PowerTorsionDerivedDescent・PowerResidueDerivedHomology）。

#### 3.4.4 未使用（639 宣言を名前で走査）

上の死んだファイルのほか：`coaugmentedHomEquiv_apply/_symm_apply`・`coaugmentedHom_ext`・`_naturality_left/right`・`coaugmentedHomEquivOfIsIso`、
`complete_two_cohomology_scalar_pow_eq_zero`、`complete_moduleMapConeScalar_pow_eq_zero`、`faithfullyFlatDerivedHomology_scalar_eq_zero_iff`、
`homologyZeroDesc_epi`・`coordinateQuotient_epi`・`minimalHomologyZeroQuotient_epi`、`koszulExtPowersComparison`、`koszulTorPowersComparison`、
`koszulModuleTorPowersComparison`、`koszulTorComparisonEquiv`、KoszulRadicalSupport の 2 定理、`regularKoszulLocalCohomologyComparison`、
`perfectRing_derivedTensor_concentrated(_of_char_eq_zero)`、`perfectRing_derivedTensorAlgebraAugmentation_isIso`、`torAlgebraComparisonNatIso`、
`length_torModule_comm`、`shortExact_iff_exists_distinguished_single_triangle` ほか。これらを消すと、ファイルの中だけで使われている補助
（LocalFlatnessCriterion の 8 個、TorSymmetry の `torOneKernel*`・`torShift*` など）も連鎖で消える。

#### 3.4.5 選択と構成

- FiniteFreeResolution の `coverRank`・`cover`・`coverπ` は `(Module.Finite.exists_fin' R M).choose…`。構造体 1 つの def か、Mathlib の表示の API に。
- MapExtend は `∃ i, e.f i = i'` の `choose_spec` を 8 回使う。`e.r` か明示の添字に。

#### 3.4.6 提出候補

左導来関手の長完全列（加群圏の間の加法関手）、平坦なら Tor が消える、Tor の零化イデアルの評価、Tor の対称性、`colim` の Additive・Linear、
`mapExtendIso`、`fromLeftDerivedZero` の関手についての自然性、局所平坦性判定、Noether 環上の Tor の有限長・台・有限性、`ModuleSubcomplex`、
DirectedHomology、`FiniteSupportCoproduct`。Auslander–Buchsbaum は上流の PR を追う（出し直さない）。

### 3.5 HA4 DerivedCompletion の塔の側（88 → 約 15 ファイル）

#### 3.5.1 統合

| 新しいファイル | 元のファイル | BS |
| --- | --- | --- |
| Tower/HolimModel | TowerComplex・TowerIso・ProductHomology・ProductCoordinates・ProductHomotopy・TowerCoordinates・TowerHomology | なし |
| Tower/Maps | TowerUnit（一般の部分）・TowerProjection・TowerMap・TowerIsoProjection・TowerIsoMapCompatibility・TowerLiftNaturality・TowerExact | なし |
| Tower/Milnor | MilnorSequence・TowerHomologyNaturality・MilnorNaturality・MilnorMapZero・MilnorAnnihilator・UniformZeroTower・UniformZeroTowerHomology・ConstantTower | MilnorAnnihilator（2） |
| Koszul/Tower（軽い） | KoszulTower・KoszulCanonicalZero・KoszulStageZero、TowerUnit の `koszulComplexInclusion`・`koszulCompletionUnit` | KoszulCanonicalZero（1） |
| Koszul/Completion | KoszulMilnor・KoszulUnitCompatibility・KoszulStageComplete・TowerComplete・TowerHomologyComplete | TowerComplete（4） |
| Localization | LocalizationPresentation・LocalizationResolution・LocalizationHomCoordinates・LocalizationTowerComparison・ScalarTowerInversion | なし |
| Reflection | ReflectionRing・ReflectionTransport・PrincipalReflectionPresentation・PrincipalReflectionComplete | 名前を使う |
| Principal/KoszulModel | PrincipalTowerPresentation・PrincipalKoszul{Stage,Product,Cone,Unit,Ring}・ScalarRestriction・PrincipalQuotientComplete | あり（`PrincipalCompletionH0` 29 回） |
| Principal/Comparisons | PrincipalCompletionDerivedComparison・PrincipalCompletionFunctor・PrincipalClassicalComparison（PrincipalIdeal は CLMST 専用なので別） | あり |
| Pair/* | Pair{TowerPresentation,TowerEvaluation,TowerUniqueness}・PairKoszul{Stage,Transition,Comparison,Product,Cone,Unit,Ring}・IteratedKoszulRing・PairIterationComparison・PairZeroCompletion | 名前を使う（§3.5.3） |
| PowerTower | PowerTorsionTower・PowerTorsionComplex・PowerImageTower・PowerCokernel{Reconstruction,Naturality,TensorModel,Transitions}・KoszulPowerCokernelComparison・PowerTowerLimitBound | なし |
| PowerTorsionTor | PowerTorsionTensor・PowerTorsionTorExtension・PowerTorsionTorConormal（Tor と正則局所環を引く。HA3 の Tor 側へ移すのが自然） | PowerTorsionTensor（1） |
| Restriction | RestrictionKoszulStage・RestrictionTower（軽い）と RestrictionComplete・RestrictionCompletionEquivalence・RestrictionCompletion（重い）に分ける | RestrictionCompletion（6） |
| IteratedTensor | IteratedAlgebraH0Comparison・IteratedTensorH0Complete・IteratedTensorQuotientComparison・IteratedTensorCartier{Algebra,LinearComparison,Products} | 使うのは BS/Prism/Tensor/PerfectPrismTensor だけ |

- TowerMap が HA5 の ComplexCompletionQuasiIso を import している。本当に必要か確かめる（不要なら Tower/* は HA5 より下に置ける）。
- IteratedTensor* は BS の PerfectPrismTensor 専用。BS 側へ移すのが自然だが、BS は別セッションの管轄なので、BS 側の作業として申し送る。
- 死んだファイル：PowerTorsionTorProduct。

#### 3.5.2 Mathlib との重なり

- Koszul 複体、holim、Milnor 列、lim¹、導来完備化はどちらの版にもない。`mulLeft_range_eq_span` は `Submodule.span_singleton_eq_range`
  の言い直し（確度高）。`complexProductHomologyEquiv` は `AB4Star (ModuleCat R)` と `HomologicalComplexLimits` から出せる（確度中）。

#### 3.5.3 一本化

- **Pair* を Principal* の反復で置き換える**：PrincipalTowerPresentation ↔ PairTowerPresentation、Principal{Reflection} ↔ PairTower{Evaluation,Uniqueness}、
  PrincipalKoszul{Stage,Product,Cone,Unit,Ring} ↔ PairKoszul{…}、さらに IteratedKoszulRing がファイル単位で並行（Pair 側は約 1900 行）。
  PairIterationComparison が pair ≅ principal の反復を証明済み。`pairKoszulCoordinates`（BS 16 回）・`PairCompletionH0`・`pairCompletionCommRing`
  （6 回）・`pairCompletionUnitRingHom` は名前として残し、定義を反復の側に移す。n 変数への一般化も同時に得られる（一般の `Fin e` の Koszul 塔
  は完備性まではすでに n 変数）。
- `principalCompletion_existsUnique_*`・`pairCompletion_existsUnique_*`・`iteratedCompletion_existsUnique_ringHom` と `*_isModuleComplete_unit_{first,second}`
  はどれも `IsCompleteModuleReflection` の例。一般の補題 1 本にする。
- UniformZeroTower・UniformZeroTowerHomology・PowerTorsionTower・PowerTorsionComplex は同じ仕組み。ConstantTower・ScalarTowerInversion は Milnor の特殊化。
- 自然性の補題（TowerHomologyNaturality・MilnorNaturality・TowerLiftNaturality・TowerIsoMapCompatibility）は 1 節に。

#### 3.5.4 未使用

`completedUnitH0PDEquiv_unit`、`complexCompletion_single_eq_koszul`、`constantComplexTowerUnitIso_inv`、`flat_powerTorsionTowerDifference_bijective`、
`iteratedAlgebraCompletionH0PDAlgEquiv_unit`、`iteratedCompletedTensorCartierH0Iso_left/_right`、`iteratedTensorCartierCompletedAlgEquiv_toAlgHom`、
`koszulPowerCokernelComparison_quasiIso`、`pairKoszulCompletionShortComplexIso_hom_τ₂`、`principalCompletionShortComplexIso_hom_τ₂`、
`scalarComplexTowerHomotopyLimit_smul_isIso`、`tor_eq_zero_of_power_torsion_and_conormal`、`tor_ideal_sq_zero_of_power_torsion_tests`。
ファイルの中だけで使われている名前が約 150（LocalizationResolution 10、PowerCokernelTensorModel 7、PairZeroCompletion 7 など）は private に。
ルート直下の一般的な名前（`shortComplexZero`・`diagonalSequence`・`sequenceDiagonal`・`sequenceShiftRight/Tail/Head`・`isModuleComplete_zero`）も private か名前空間へ。

#### 3.5.5 選択と構成

- 一意存在の定理から `.choose` で写像を作っている：PrincipalCompletionFunctor（L54・66）、PairIterationComparison（L23–55）、PairZeroCompletion（L29・41）、
  PrincipalClassicalComparison（L71）。既にある `IsCompleteModuleReflection.liftAlgHom` を使う。`_comp`・`_unit` の補題が rfl に近くなる。
- ReflectionRing の `surjective` の `.choose` は `Function.surjInv`、PrincipalReflectionComplete の `mkQ_surjective` の `.choose` は `Quotient.out` に。

#### 3.5.6 提出候補

ℕ 塔の holim `mappingCone(1 − shift)⟦-1⟧` と Milnor 列（AB4* のアーベル圏へ一般化して）、AB4* での homology と積の可換、一様零の塔と定数塔の
lim・lim¹、望遠鏡による `R[1/a]` の長さ 1 の自由分解、`IsCompleteModuleReflection` から環構造。導来完備化が上流に入った後に：正則主イデアルの
導来完備化の H⁰ ≅ `AdicCompletion`、完備化と係数の制限の可換。

### 3.6 HA5 DerivedCompletion の完備化の側（104 → 約 15 ファイル）

#### 3.6.1 統合

| 新しいファイル | 元のファイル | BS |
| --- | --- | --- |
| ModuleComplete/Basic | Basic・Module・AdicComparison・ModuleClosure・ModuleHomComplete・Torsion・FinitePresentationComplete・DivisibleHomZero・Jacobson・BoundedTorsionComparison・CompleteSequenceSum、HA4 の `adicRecurrenceEquiv` | `IsModuleComplete`（35） |
| ModuleTower | ModuleTower・ModuleTowerEquiv（AdicTower は削除） | なし |
| ConeAPI | ConeShortExact・ConeBoundaryNormalization（ModuleConeCoordinates・ModuleConeNaturality は 6 行の再エクスポートなので削除し、importer 4・7 本を付け替える） | なし |
| ComplexCompletion | ComplexCompletion・…QuasiIso・…Derived・…Naturality・…Reconstruction・…HomologyComplete・Closure・TermwiseComplete | あり |
| CompletionReflection | CompletionReduction・DerivedKoszulReduction・ComplexCompletionReflection・CompletionTriangulated・KProjectiveProduct・ModuleResolution | あり |
| BoundedAboveCompletion | BoundedAboveCompletion・…Equivalence・CompletionUpperBound・CompletionH0Comparison・CompletionHomologyDivisibility | あり |
| CompletionMonoidal | CompletionTensorComparison・CompletionTensorCoherence・CompletionAlgebraObjects・CompletionH0Algebra・…Universal・CompletionPointAction（重いので BoundedAboveCompletion と分ける） | あり |
| CompletedTensorVanishing | CompletedTensorZero・CompletedTensorModuleAction・CompletedBaseChangeTriangle・CompletedModuleShortExact・CompletedTensorShortExact | あり |
| CompletionQuotient | CompletionQuotient・CompletionQuotientBaseChange・CompletionScalarConeComparison・RegularTensorReduction | あり |
| CompletedBaseChange | CompletedBaseChangeScalar・CompletedTensorCoefficient・CompletedBaseChangeH0Coefficient・AlgebraBaseChangeTensorUnit | あり |
| CompletedAlgebraH0 | CompletedAlgebra{Restriction,ScalarAction,UnitNormalization,PrincipalComparison,PDComparison}・CompleteFirstPairComparison・CompletionH0PrincipalComparison・CompletedTensor{AugmentationCriterion,PDComparison,H0Comparison,ClassicalComparison,H0RingTransport}・CompletedSurjectiveAlgebraMul（一本の鎖） | あり |
| ModulePower | ModulePower{Reduction,TensorModel,DerivedComparison,TensorHolim,HolimNaturality,TorComparison,TensorTorZero,TorsionBound}・BoundedTermTorsionComparison・FiniteCoefficient{PowerComparison,PowerHolim,CokernelHolim}・FiniteTensorComplete | CLMST |
| TorAlgebraComplete | ModulePowerTorAlgebra{Tower,Almost,Milnor}・TorAlgebraMilnor{Actions,Middle,Sequence}・TorAlgebraComplete | CLMST |
| DerivedPurity | CompleteScalarConePurity・CompleteFlatReductionPure・CompleteFlatReductionBounded・DerivedPowerCokernelModel・CompleteMilnorAnnihilator・RegularCompletionPure・PerfectResidueCompletedTensor | あり（多い） |
| IdealExtension | CompleteIdealExtension・ConormalIdempotentImage・ConormalExtension・TorOneCompleteExtension・CompletedQuotientTensorExtension | あり |

- PDCompletion（BS 33 ファイル）は名前もパスも当面そのまま。HA4 の Pair の置き換えと合わせて扱う。
- 層の注意：ComplexCompletionReconstruction は HA4 の TowerExact・LocalizationTowerComparison を import する。CompletedTensorShortExact は
  ModulePowerDerivedComparison を import する。FinitePresentationComplete は HA4 の ReflectionTransport が要る。
- 死んだファイル：AdicTower（audit_clmst の `assert_no_sorry` だけ。監査の行も消す）、CompletedTensorModuleReduction、FlatResidueLimitTorsion。

#### 3.6.2 Mathlib との重なり

- `adicTowerTransition` は `AdicCompletion.transitionMap`、`adicTowerLimitEquiv` の行き先はすでに `AdicCompletion`（ファイルごと削除）。
- `mem_jacobson_bot_of_isModuleComplete` は `IsAdicComplete.le_jacobson_bot` の導来版（仮定が弱いので重複ではない）。
- `boundedAboveCompletionCommMonFunctor`・CompletionTriangulated は Mathlib の `Functor.mapCommMon`・`ObjectProperty.IsTriangulated` を正しく使っている。
- `coneStandardShortComplex` は `CochainComplex.mappingCone` の API・DegreewiseSplit と一部重なる見込み（確度低〜中）。

#### 3.6.3 一本化

- **PD の d = 0 経由の H⁰ 同型**：`PDCompletionH0 B p 0` は `PairCompletionH0 (p) 0` で、principal の完備化に行くための遠回り。
  `completedTensorH0PDAlgEquiv`・`…OfIso`・`…OfTor`・`…OfKoszul` は型が同じで、一致を示す `…_eq_of*_apply` 3 本は未使用。
  `completedTensorH0AlgEquivOfKoszul` は一般の `a` の版、`completedTensorH0PrincipalRingEquiv`・`…AdicRingEquiv` は d = 0 経由、
  `completedAlgebraH0PDAlgEquiv`・`…PDBAlgEquiv` と `completedAlgebraPrincipalH0AlgEquiv`、`completionH0PrincipalAlgEquiv` と同、
  `completionH0PairAlgEquivOfCompleteFirst` と `pairCompletionPrincipalAlgEquivOfCompleteFirst` が重複。
  → `derivedH0AlgEquivOfIsoHomology` 型の輸送 1 本と、principal と pair(·, 0) をつなぐ補題にまとめ、PD の d = 0 の層をなくす。BS が使う
  `completedTensorH0AdicRingEquiv(_left/_right/_algebraMap)` は名前を残す。
- 複体の水準と導来の水準の並行：`complexCompletionReductionIso/NatIso` と `derivedComplexCompletionReductionIso/NatIso`、
  `derivedComplexCompletionFunctor`（D(R)）と `boundedAboveDerivedCompletionFunctor`（D⁻）。
- 「完備化は、完備性を保つ完全関手と可換」の Comparison・`_unit`・`_isIso`・Iso・`_naturality`・NatIso の型が 3 回（CompletionScalarConeComparison・
  CompletionQuotientBaseChange・CompletionReduction）。一般の補題 1 本に。
- `modulePowerTorAlgebraLimitComparison`・`LimOneComparison`（Tower、未使用）と `modulePowerCokernelTorAlgebraLimitComparison`・`LimOneComparison`（Milnor）。
- `completedAlgebraBaseChangeTensorIso` と `completedBaseChangeTensorH0Iso`。

#### 3.6.4 未使用

`isComplete_Q_of_termwise_pow_smul_zero`、`boundedAboveDerivedCompletionInclusionIso`、`completeComplex_homology_pow_annihilated`、
`completedBaseChangeTriangleIso`、`completedTensorH0AlgEquivOfKoszul_unit/_left/_right`、`completedTensorH0PDAlgEquivOfIso_left/_right`、
`completedTensorH0PDAlgEquiv_eq_of{Iso,Tor,Koszul}_apply`、`completedTensorH0LeftScalarTower`、`completionH0_existsUnique_algHom`、
`completionQuotientBaseChangeNatIso`・`completionScalarConeNatIso`・`complexCompletionReductionNatIso`・`derivedComplexCompletionReductionNatIso`、
`complexCompletionUnitNatTrans`、`derivedComplexCompletion_existsUnique_extension`、`completeReflectorAdjunction_unit`、
`isUnit_one_sub_mul_of_isModuleComplete`、`isModuleComplete_of_natCast_pow_smul_zero`、`isModuleComplete_quotient_span_pow`、
`moduleTowerLimit_flat_residues_power_torsion_bound`、`modulePowerTorAlgebraLimitComparison`・`…LimOneComparison`、
`torAlgebraMilnorShortComplex_restrictIso`、未使用の `*_unit` 補題 9 本ほか。`_apply` には `@[simp]` のものがあるので消す前に確かめる。

#### 3.6.5 選択と構成

- `pairCompletionToPrincipalOfCompleteFirst`・`principalCompletionToPair`（CompleteFirstPairComparison）と `completionH0PrincipalAlgEquiv` の中は
  一意存在の `.choose`。既存の `completionH0AlgebraLift` のような持ち上げの def にし、一意存在は「持ち上げ＋ext」の系にする。
- `adicRecurrenceEquiv` を ModuleComplete/Basic へ下ろす（CompleteSequenceSum がこの 1 定義のために Principal のファイルを import している）。

#### 3.6.6 提出候補

`ModuleTower` の差分写像と極限、`moduleTowerDifference_surjective`、lim¹（加群の Mittag-Leffler 型）、`ideal_mod_power_idempotent_of_conormal_surjective`、
`algHomOfDenseLinearExtension`、`hom_eq_zero_of_scalar_zero`、`isUnit_one_sub_mul_of_recurrence_bijective`、`exists_power_torsion_bound_of_noetherian`・
`flat_tensor_power_torsion_bound`、ConeShortExact（Mathlib になければ）、KProjectiveProduct。長期：導来 I 完備性（`R_f` への Ext の消滅、三角形で閉じる、
正則・有界ねじれでの `IsAdicComplete` との比較、Stacks 091N・091P）。

### 3.7 順序の案

BS の再ビルドの量で二層に分ける。

1. **第一層（BS に触れない）**：BS が import しないファイルだけを動かす。死んだファイルの削除、未使用の宣言の削除、Mathlib への置き換え
   （確度高のもの）、HA1 の大部分（Complex/*・Tensor/*・LinearYoneda・ComplexColimits・MinimalResolution）、HA3 の CLMST 側
   （Koszul/ParameterAnnihilators・LocalCohomology/*・Resolution/FiniteFree）、HA4 の Tower/*・Localization・PowerTower、HA5 の ModulePower・
   TorAlgebraComplete（CLMST だけ）。BS が import するファイルの中身は変えない。
2. **第二層（BS の再ビルドを伴う）**：DerivedCompletion の BS 向けのファイルの統合、Pair の置き換え、PD の d = 0 の層の整理、導来テンソルの一本化、
   `.choose` の def 化（BS が使う名前のもの）。CommutativeAlgebra で保留している「BS の再ビルドの一括作業」（Koszul・KoszulResolution の移動、
   BS が import する X 群の 3 本）とまとめて 1 回にする。BS のセッションと時期を合わせる。

第一層の中は HA1 → HA3 → HA2 → HA4 → HA5 の順（import の下から）。各群の中では死んだファイル・未使用の削除を先にし、統合はその後。

### 3.8 決定（記録）

1. ~~Auslander–Buchsbaum を残すか削除するか~~ → 削除（2026-10-30）。**訂正（同日、作業時の再確認）**：`AuslanderBuchsbaum` は
   CA/RegularLocalRing/Criterion（極大イデアルの射影次元による正則性の判定）が使い、それを RegularLocalRing/Localization が使うので削除しない。
   RegularQuotientProjectiveDimension の `projectiveDimension_eq_quotient` も同じ経路で使う。RQPD からは AuslanderBuchsbaum の import を外し（Mathlib の import だけで足りる）、
   Criterion が直接 import するようにした。
2. ~~StupidTruncation の置き換え~~ → Mathlib を上げるまで保留（2026-10-30）。
3. ~~Tensor をどちらに寄せるか~~ → 本体は `HomologicalAlgebra/CochainTensor/`（Basic・Symmetric・Shuffle・DegreeMaps・ShortExact・BaseChange・
   Cone/Shift/Single/Acyclic）。PerfectComplex には完全複体などの固有部分だけを残し、殻 21 本は PC2 で削除。`cochainTensor` は名前を残し、
   ほかは Mathlib の記法へ段階的に寄せる（利用の多いものは `@[deprecated] alias`）。PC2 と同時に行う（2026-10-30）。
4. ~~IteratedTensor*~~ → コーディネータが `BhattScholze/Prism/Tensor/` の下へ移す（BhattScholze/ を編集しない決まりの、この件だけの例外。2026-10-30）。
   第二層の作業時間に合わせて行う。
5. ~~第二層の進め方~~ → (a)：BS の作業の区切りに時間を決め、BS 側の編集を止めて第二層をまとめて行い、全体ビルド 1 回でコミットする。
   CA で保留している BS の再ビルドの作業も同じ時間に行う。準備（スクリプト）は第一層の間に済ませる（2026-10-30）。

## 第4章 PerfectComplex

### 4.1 群の分け方

| 群 | 内容 | ファイル数 |
| --- | --- | --- |
| PC1 | 基礎：完全複体、閉台、K₀、Euler 標数、分解、Koszul、長さ | 45 |
| PC2 | テンソル積：二重・三重・六重、shuffle、巡回和 | 36 |
| PC3 | 作用と固有分解：位数 3 の作用（Cubic*）、Fourier、involution（位数 2）、冪等元 | 43 |

BS への依存は三群とも直接・推移的にない。CLMST は PC1 の 11 ファイルに LengthAlgebra 経由で推移的に依存する（§4.2）。

KTheory へ回すもの（PC1 の IntegerEuler 系・Adams の Koszul・FiniteProjectiveResolutions）は第6章で受け入れる。

### 4.2 PC1 基礎

規模：45 ファイル、5868 行。中身は 6 つの層が混ざっている：(a) 正規化長さ、(b) 自由モデル（論文 Lemma 3.5 の語彙）、
(c) 有限射影ホモトピー圏、(d) 閉台 K₀、(e) Koszul 長さの評価、(f) KTheory に依存するもの。
BS への依存はない。CLMST は直接 import しないが、LengthAlgebra 経由で 11 ファイル（Basic・Closure・K0・NormalizedEuler・
NormalizedLength・NormalizedLengthComap・OrdinaryEuler・QuotientLength・SupProperty・SupPropertyComap・Support）に推移的に依存する。
NormalizedLength を変えると 587 モジュール（うち CLMST 27）、Basic・Support・K0 はそれぞれ約 500 モジュールが再ビルドになる。

#### 4.2.1 統合（45 → 約 15 ファイル）

| 新しいファイル | 元のファイル |
| --- | --- |
| （削除） | 互換用の import ファイル 4 本：CochainBiproduct・ConeArrowMap・DegreewiseKernelLift・TwoTermScalarMap（利用者は HomologicalAlgebra.Cochain* を直接 import する） |
| Free/Support | Basic（IsSupported、twist）・Support |
| Free/K0 | Closure・K0（IsPerfectSupported、PerfSupp、K0Supported） |
| Free/Euler | Basic の `chiOrd`・`chiLam` の定義・NormalizedEuler・OrdinaryEuler |
| Free/KoszulGeneration | KoszulGeneration（そのまま） |
| Perfect/HomotopyCategory | HomotopyCategory・BaseChange・DegreewiseRetract・BiproductPerfect の strictlyPerfect の部分・ClosedSupportRelations 冒頭の K 射影性の 2 補題 |
| Perfect/FreeComparison | K0Comparison・K0Functoriality |
| Perfect/KoszulTower | KoszulTower（そのまま） |
| ClosedSupport/Basic | ClosedSupport・`HasHomologySupportOn.biprod` |
| ClosedSupport/K0 | ClosedSupportK0・ClosedSupportCongr・ClosedSupportRelations・ConeAdditivity・ClosedSupportBiproduct の `mk_biprod`（`mk_tensor` は PC2 の ClosedSupportCup へ） |
| ClosedSupport/Functoriality | ClosedSupportFunctoriality・ClosedSupportComparison |
| KoszulLength | KoszulLengthBounds・ProjectiveBounds・KoszulAmplitude・MinimalLowerBound |

- 外へ：正規化長さ（NormalizedLength・NormalizedLengthComap・SupProperty・SupPropertyComap・QuotientLength。複体を使っていない）→
  LengthAlgebra（例 `LengthAlgebra/Normalized/`）。IntegerEuler・IntegerEulerIso・CoefficientEuler（KTheory の HomologyEulerBasic・
  SupportedCoefficients を import）と namespace `Adams` の KoszulOneModel・KoszulTensor・KoszulClasses（利用者は KTheory/Adams だけ）→
  KTheory。FiniteProjectiveResolutions（KTheory から 20、InfinityCategories から 4）→ KTheory。AsymptoticLengthBounds・
  ResolutionFamilies → Asymptotic。FinThreeBiproduct（利用者は CubicActionTensorClass だけ）→ §4.2.3 の一般化か Cubic 側。
- 循環：BiproductPerfect が import している互換ファイル `PerfectComplex.IdempotentDecomposition` を外し、HomotopyCategory と
  ClosedSupport を直接 import すれば閉路は 0（そのままだと IdempotentImage → ClosedSupportRelations で閉路）。

#### 4.2.2 Mathlib との重なり（固定版と最新版で差なし）

- `finiteProjective_exists_retract` の本体 → `Module.Finite.exists_comp_eq_id_of_projective`（RingTheory/Finiteness/Projective.lean）。確度高。
- `strictlyPerfectComplex_isKProjective`（利用 12）・`strictlyPerfectComplex_quasiIso_iff`（利用 9）は
  `CochainComplex.isKProjective_of_projective`・`IsKProjective.quasiIso_iff` の包み。利用が多いので残す。
- `chiOrd`・`lambdaEuler` の交代和は Mathlib の `HomologicalComplex.homologyEulerChar`・`ComplexShape.EulerCharSigns` と同じ形だが、
  Mathlib 側は finrank 専用。符号を `EulerCharSigns` に揃えることはできる。
- `IsPerfectSupported.bounded`（∃ a b）の繰り返しを `IsStrictlyGE`・`IsStrictlyLE`（プロジェクトの `strictlyBoundedComplex`）に統一。
- `HasFiniteProjectiveResolutions` は Mathlib の `ObjectProperty.hasFiniteResolutionOfLength`・`HasProjectiveDimensionLE` で
  言い換えられる可能性（確度中）。
- Mathlib にないもの：三角圏の K₀（プロジェクトの CategoryTheory/TriangulatedK0）、Serre 類についての homological kernel。

#### 4.2.3 一本化（群の中で同じ構成が繰り返されている箇所）

- K₀ のモデルが 3 つ（自由モデル `K0Supported`、列で台を指定した `TriangulatedK0 (SupportedPerfectHomotopy z)`、閉台の
  `K0WithSupport Z`）と比較が 2 つ。基底変更と群作用もそれぞれに書かれている。一般形は K₀ を `K0WithSupport Z` だけにし、
  列の台は Z = V(z)、ひねりは環自己同型に沿った `K0WithSupport.map`、自由モデルは「局所環上では有限自由な代表がとれる」補題に格下げ。
  ただし `K0Supported` は Inputs/Descent の引用（`theorem_3_1_K0`）と Paper/Lemma3_5 の文に現れるので、引用の文言を変える判断が要る。
- 台の条件が 4 つ（IsSupported、`scalarSupported`、HasHomologySupport I、HasHomologySupportOn Z）。本体は HasHomologySupportOn だけにし、
  IsSupported は有限射影複体での同値補題として残す。`HasHomologySupport I` は `HasHomologySupportOn (supportZeroLocus I)` と Iff.rfl
  （外部利用 8）なので abbrev か削除。
- 閉包補題が 4 系統 × 6 操作（iso・shift・zero・mappingCone・baseChange・twist）。「複体の ObjectProperty が iso・シフト・錐で
  閉じていれば三角部分圏と K₀ が得られる」を一度示し、`⊓` で組み合わせる。閉台については Serre 版 homologicalKernel を使う。
  `perfectHomotopySupportedOn` の `IsTriangulatedClosed₃` は既存の `homotopyProperty_isTriangulatedClosed₃` と同じ議論の繰り返し。
- 双積の類の公式が二項版（`mk_biprod`）と Fin 3 専用版（`mk_finThreeBiproduct`）。`[⨁ i, P i] = ∑ i, [P i]`（Fintype 添字）一本に。
- Euler 評価が 4 種類（`chiOrd`・`chiOrdHom`・`integerEuler`・`lambdaEuler`/`chiLam`）。加法的な長さ λ についての `lambdaEuler` 一本にし、
  整数値の版はキャストとの両立補題に。ただし CLMST/SourceEulerEvaluation が `unfold lambdaEuler chiOrd` と `toReal_toENNReal` を
  使っているので、`chiOrd` の定義を変えると壊れる。
- O と o の対が 4 組そのまま複写されている。「v ≤ Σ r·c で c が有限なら O」を一本にし、o は `.trans_isLittleO` で合成する。
- 自由版と直和因子版が並んでいる（`lambdaHomology_koszulComplexOn_le_sum` と `_of_retracts` など）。直和因子版だけを残し、
  自由版は `Retract.ofIso` で導く。`lambdaHomology_ne_top_of_retract` は `ne_top_of_le_ne_top` と `lambdaHomology_le_of_retract` の組合せ。
- Koszul 複体の所属を示す補題が 3 つの K₀ モデルそれぞれにある（`koszulPerfSupp`、`perfectKoszulObj`、`koszulClass`）。
- `strictlyPerfectComplex_biprod` と `HasHomologySupportOn.biprod` は分裂短完全列の特殊例として導ける。
- `NormalizedLength.restrict`・`comap`・`restrictToBase` を一本の `comap` に（CLMST が `lam.comap f _ le_rfl` を使うので旧シグネチャは
  包みとして残す）。単調性の補題群は CategoryTheory/AdditiveLength と CommutativeAlgebra/PowTorsionCategory の組合せと重複。
- `twist` の補題群は `baseChange_smul_iso_twist` を通せば基底変更の補題から導ける。

#### 4.2.4 未使用

- 削除候補：`perfectKoszul_homological_vanishing`、`exists_common_pow_annihilator_of_homologySupport` とそれだけが使う
  `homology_pow_torsion_of_support`、`mk_degreewise_shortExact`、`freeToClosedSupportK0_map`、`scalarClosedSupportK0Equiv_mk`（`@[simp]`）、
  `resolutionFamily_term_iso`、`resolutionFamily_rank_isLittleO`、`perfectK0_smul_mk`。
- 慎重に扱う：rfl の `@[simp]`（`hasHomologySupportOn_zeroLocus`、`restrict_len`、`cochainFinThreeProjection_zero/one/two`）、instance
  （`hasFiniteProjectiveResolutions_regular`、`perfectK0DistribMulAction` は `g • x` の解決に暗黙に使われる）。
- 再利用価値：IntegerEulerIso の後半（`integerEulerEquiv` : K₀^m(R) ≃+ ℤ など）は外部未使用だが定理としてきれい。外部で使われているのは
  `maximalFreeClosedSupportEquiv` と `maximalSupport_hom_ext_koszul`（KTheory）だけ。`integerEuler_mk` は `@[simp]` にする価値あり。

#### 4.2.5 提出候補

1. 加法的な長さ関数についての Euler 標数と、写像錐・短完全列での加法性（Mathlib の EulerCharacteristic.lean を finrank 以外へ一般化）。
2. 有界な有限射影複体（K^b(proj)）の ObjectProperty と `IsTriangulated`、K 射影性・擬同型とホモトピー同値の一致。
3. Serre 類 S とホモロジー関手 H について {X | ∀n, H(X⟦n⟧) ∈ S} が三角部分圏（Mathlib の `homologicalKernel` の一般化）。閉台条件の
   instance がすべてここから出る。
4. 三角圏の K₀（CategoryTheory/TriangulatedK0、別の群の管轄）。
5. 確度中：`Module.support` の閉集合版の補題、`ennreal_isBigO_of_le_sum_nsmul` 型の漸近評価。

#### 4.2.6 リスク

- 変えない名前：CLMST が参照する `NormalizedLength`、`.comap`、`IsPowTorsion.comap`、`lambdaEuler`（6 ファイル 15 箇所）、`chiOrd`、
  `toReal_toENNReal`。
- 監査スクリプトが宣言名を直接書いている：`scripts/audit_triangulated_k0_shift_shared.lean`（`mk_shift`）、
  `scripts/audit_homotopy_cone_representative_shared.lean`（`perfectFreeRepresentative_triangle`・`perfectToFreeK0`・
  `ClosedSupportShortExactAdditive`）、`scripts/audit_clmst.lean`（`HasSup`・`NormalizedLength`）。
- IntegerEuler 系は KTheory.HomologyEulerBasic → ClosedSupportK0 に依存するので、PerfectComplex 側に残したまま統合しない。
- Basic・Support・K0 は約 500 モジュールの上流。統合は一回の全依存ビルドにまとめる。

### 4.3 PC2 テンソル積

規模：36 ファイル、約 1300 行。うち 21 本は 5〜8 行の互換スタブで、`HomologicalAlgebra/CochainTensor*.lean`（34 本、3435 行）を
再輸出しているだけ。テンソル積の構成そのもの（二重・三重・四重・六重、shuffle、対称性、六角形、回転）は HomologicalAlgebra 側にある。
BS/CLMST は PC2 の 36 本を import しない。参照は HomologicalAlgebra の `cochainTensor` と `cochainTensor_isStrictlyLE` の 2 つだけ
（BS の RootEnvelope/Source・Andre/Envelope/MonicSource・PowerRootEnvelope/Unconditional/Source）。

#### 4.3.1 統合

| 新しいファイル | 元のファイル |
| --- | --- |
| （削除） | 互換スタブ 21 本：Tensor・TensorBoundedAbove・TensorCone・TensorDegreeMaps・TensorHomogeneous・TensorScalarCoordinates・TensorShift・TensorShortExact・TensorShuffle・TensorShuffleEquivariance・TensorSingle・TensorSix{Homogeneous,Rotation,Shuffle,ShuffleEquivariance}・TensorSymmetry・TensorTriple・TensorTriple{BaseChange,DegreeMaps,Differential,ShortExact}。利用者の import を HomologicalAlgebra の実体へ張り替える（Tensor.lean は ClosedSupportRelations も再輸出しているので、TensorPerfect と TwoTermScalarMap にその import を足す） |
| Tensor/Perfect（約 160 行） | TensorPerfect・TensorHomotopy・TensorAcyclic・TensorSupport |
| Tensor/CyclicSum（約 290 行） | CochainCyclicThree・TensorTripleCyclicSum{,Perfect,Eigen,Class}（PC3 の CubicAction と一体で動かす案も） |
| ClosedSupportCup | TensorK0・TensorEnlarge・TensorBaseChange（`K0WithSupport.cup`。PC1 の ClosedSupport/K₀ と同居） |

- 外へ：TensorTorComparison → IntegerEuler・IntersectionMultiplicity（唯一の利用者は AdamsVanishing）。TensorResolutionLength →
  NormalizedLength・Asymptotic（テンソル複体の話ではない。利用者は Paper/Section2/TowerApproximation と MinimalLowerBound）。
  RankOneTensorTripleExt → 唯一の利用者 KTheory/Adams/KoszulCubeExt に吸収するか ModuleCat の一般ファイルへ。
- HomologicalAlgebra 側の統合案（HomologicalAlgebra の見直しへ申し送り）：`HomologicalAlgebra/CochainTensor/` に
  Basic（Tensor・Linear・Bounds・Finite・Projective）、Symmetric（Symmetry・Hexagon・Braided）、Shuffle（Shuffle・Homogeneous・
  ShuffleEquivariance・Triple・Six*）、DegreeMaps、ShortExact、BaseChange、Cone・Shift・Single・Acyclic。

#### 4.3.2 Mathlib との重なり（固定版と最新版で差なし）

- 既に Mathlib の単項的構造（Algebra/Homology/Monoidal.lean）の薄い包み（確度高）：`cochainTensor` = `HomologicalComplex.tensorObj`（`⊗`、
  107 ファイル、BS 3）、`cochainTensorMap` = `⊗ₘ`（88）、`cochainTensorIso` = `tensorIso`、`cochainTensorAssociator` = `α_`、
  単位・単位子 = `𝟙_`・`λ_`・`ρ_`、`cochainTensorMap_comp` = `tensorHom_comp_tensorHom`、`cochainTensorMap_id` = `id_tensorHom_id`、
  `cochainTensorMap_add_left` = `MonoidalPreadditive.add_tensor`。`cochainTensor` は BS が使うので残し、それ以外は段階的に記法へ寄せる
  （利用の多いものは `@[deprecated] alias` を経由）。
- `cochainTensorSymmetry` は `β_` そのもの（自前の `cochainTensorSymmetricCategory` インスタンス）。Mathlib に Koszul 符号付きの
  組みひもは HomologicalComplex 上にない。部品（`mapBifunctorFlipIso_hom_naturality`、`totalFlipIso`）で naturality を短くできる（確度中）。
  `cochainTensorSymmetry_inv` は `SymmetricCategory.braiding_swap_eq_inv_braiding` から（確度高）。
- `cochainTensorShuffle P Q T U` は `MonoidalCategory.tensorμ P Q T U` と同じ（確度高）。四変数の `cochainTensorShuffle_symmetry` は、
  Mathlib にある特殊形 `SymmetricCategory.tensorμ_braid_swap` から（P Q P Q）の形が出る（確度中）。
- `cochainTensorSixShuffle` は μ を二回重ねたもの（`tensor_μ`）。`_rotation` は「`tensor C` が組みひも付き」と μ の結合律から出る
  （Mathlib に `(tensor C).Braided` のインスタンスはない）。
- `cochainTensorRotation_cube`（回転の三乗が恒等）は六角形と β² = 1 から。
- `cochainTensorDegreeMap` は `GradedObject.Monoidal.tensorHom` の成分（確度中）。
- 線形性の instance `complexMonoidalPreadditive`・`complexMonoidalLinear` は自前（Mathlib にない）。

#### 4.3.3 一本化

- whisker の ext 補題 4 本（`cochainTensorX_whiskerRight_hom_ext` など）は、余積を保つ関手 G についての一本に（確度高）。
- `apply_ι_of_sum` 型の補題 7 種類を、中間次数を一般の s で書く基本形にそろえる。
- 二重版と三重版の並行（DegreeMaps・ShortExact・ScalarCoordinate・BaseChange）：二重版を「固定した複体との `tensorLeft`・`tensorRight`
  関手」の性質として書き、三重版は合成で得る。短完全列は「次数ごとに分裂する短完全列を加法的関手が保つ」一本に。
- 符号付きの元計算による組みひも・結合子の等式（`cochainTensorShuffle_exchange_sign`、`cochainTensorSixShuffle_rotation_sign`、
  `cochainTensorRotation_cube` など）：元計算が本当に要るのは六角形と β² = 1 だけ。「対称圏で X ↦ X^{⊗n} は対称モノイダル関手で、
  μ は Sₙ 同変」という一般論を一度書けば、二乗・三乗は具体化になる（HomologicalAlgebra 側で約 500 行減る見込み）。
- 台・完全性の補題の組（`*_perfect`・`*_support`）は「strictly perfect で台が Z の複体全体はテンソルと直和で閉じる」を
  ObjectProperty として一度宣言する。

#### 4.3.4 未使用

- 削除候補：`K0WithSupport.cup_enlarge_left`・`_right`、`cup_add_left`・`_right`、`tensorClass_concrete`、
  `moduleRankOne_smul_generator`（private 化でも可）。HomologicalAlgebra の `cochainTensor_d_comp_d`（参照 0）。
- 残す：`K0WithSupport.cup_comm`・`cup_assoc`、`tensorResolutionTorIso`。
- private 化：TensorResolutionLength・TensorTorComparison の証明の段（外部で使うのは `integerEuler_cup_resolutions_of_finiteTensor` など）、
  `cochainTensorScalarNullHomotopy`、cyclic sum の補助の同型。

#### 4.3.5 提出候補

1. Koszul 符号付きの `SymmetricCategory (CochainComplex C ℤ)`（Riou の BifunctorFlip・TotalComplexSymmetry の続き。六角形の証明を
   ModuleCat の元から圏論的な証明へ書き直す必要がある）。価値が最も高い。
2. `MonoidalPreadditive`・`MonoidalLinear (HomologicalComplex C c)` と `smul_tensor` 型の補題。
3. 対称圏 C について `(tensor C).Braided`、四変数の `tensorμ` と組みひもの可換性、巡回回転の三乗が恒等。
4. 組みひも付きモノイダル関手 F について `F.mapHomologicalComplex` も組みひも付きモノイダル。
5. 有界な平坦複体とのテンソルが擬同型を保つ（HomologicalAlgebra の CochainTensorAcyclic）。

#### 4.3.6 リスク

- BS の再ビルドは起きない見込み（推移的閉包は `lake` のグラフで要確認）。HomologicalAlgebra の `cochainTensor`・`cochainTensor_isStrictlyLE`
  は改名しない。
- `cochainTensorShuffle` を `tensorμ` に置き換えると、`change` で書かれた元計算（`_apply_ι` 系）が壊れうる。先に圏論的な等式を用意する。
  利用者は KTheory/Adams の約 15 ファイル（`cochainTensorRotationIso` 13、`cochainTensorShuffle` 10）。
- `set_option backward.isDefEq.respectTransparency false` を統合後のファイルでそろえる。

### 4.4 PC3 作用と固有分解

規模：43 ファイル、2266 行（Cubic 21 本 1395 行、Involution 9 本 696 行、Idempotent 13 本 175 行。Idempotent のうち 8 本は 5〜6 行の
互換 import ファイル）。土台は `HomologicalAlgebra/CochainIdempotent*`（12 本、779 行）で、この群はその上に完全性・台・K₀ 類を足した層。
利用者は KTheory/Adams（TensorSquare* 11、TensorCube* 8、KoszulCube* 4 など）と PerfectComplex の CochainCyclicThree・TensorTripleCyclicSum*・
BiproductPerfect・ClosedSupportBiproduct・FinThreeBiproduct。BS/CLMST の import・参照はない。

#### 4.4.1 統合（`PerfectComplex/Eigen/`）

| 新しいファイル | 元のファイル |
| --- | --- |
| （削除） | 互換 import 8 本：IdempotentDecomposition・FiniteSum・Image・ImageFunctor・ImageIso・ImageQuasiIso・ImageShortExact・Sum（利用先は HomologicalAlgebra.CochainIdempotent* を直接 import） |
| Eigen/Idempotent（約 130 行） | IdempotentImagePerfect・IdempotentImageClass・IdempotentImageTrivial・IdempotentTensor |
| Eigen/Involution（約 250 行） | InvolutionDecomposition・Maps・AntiEquivariance・ShortExact・BaseChange・Class・ClassAcyclic・ClassShortExact |
| Eigen/InvolutionTensor（約 250 行） | InvolutionTensor・InvolutionTensorClass |
| Eigen/Cubic（約 400 行） | CubicActionBasic・Projector・Decomposition・Character・Eigenvectors・Transport・BaseChange |
| Eigen/CubicClass（約 300 行） | CubicActionClass・ClassMaps・ShortExact・BiproductClass・ScalarClass・IdentityClass |
| Eigen/CubicTensor（約 300 行） | CubicActionTensor・TensorProjectors・TensorRows・TensorEigen・TensorClass |

- CubicFourierTransform・CubicFourierEigen（184 行）は群外からの参照がない（KoszulCubeFourierOne が import するだけ）。削除候補。ただし
  §6.3.3 は「Fourier 座標を行列 F で計算する」ためにこのファイルを使う案を出しているので、KT2 の作業と合わせて
  「環 R 上の位数 n の巡回群の離散 Fourier 変換」として作り直すか削除するかを決める。
- 外へ：CubicFourierMinorIdentities の残り 4 本（純粋な環の恒等式、KTheory/Adams だけが使う）と `cubicCharacter*` → CommutativeAlgebra の
  CubicCyclotomic（`cube_eq_one_of_cubic_relation` の隣）。`K0WithSupport.mk_eq_zero_of_isZero` → ClosedSupport/K0。
  CochainCyclicThree・TensorTripleCyclicSum*・FinThreeBiproduct は Eigen/ に合流させてよい。HomologicalAlgebra/CochainIdempotent* の統合
  （例 3 本へ）は HomologicalAlgebra の見直しで行う。
- 循環：BiproductPerfect・ClosedSupportBiproduct・FinThreeBiproduct は互換 import を経由してこの群の下層に依存している。Eigen/Idempotent は
  この 3 本に依存させず、CubicClass・InvolutionTensor・CubicTensor は上層に置く。

#### 4.4.2 Mathlib との重なり（固定版と最新版で差なし）

- `cubicCharacter t j := t ^ (j : ℕ)` は `AddChar.zmodChar 3 ht j`（確度中。証明 `ht` を引数に取るので KTheory 12・PC 67 箇所の書き換えが要る）。
- 指標射影の直交性と和が 1（`characterProjector_orthogonal`・`sum_character_projectorMap`）は環 `End K` の `CompleteOrthogonalIdempotents`
  （RingTheory/Idempotents.lean）そのもの。`End K` には `Ring`・`Algebra R` のインスタンスがある。射影はすべて τ の多項式で可換なので
  積の順序は問題にならない。
- `map_invOf_two`・`map_invOf_three` は `map_invOf` と `map_ofNat` から一般形 1 本に（確度高）。
- `scalarMatrixThree` = `Matrix.toLin'`、`cubicVectorRotation` = `LinearMap.funLeft`（どちらも未使用なので削除が先）。三点の Fourier 変換は
  `ZMod.dft` に当たるが係数が ℂ 限定。指標の和の補題 `AddChar.sum_eq_ite`・`IsPrimitiveRoot.geom_sum_eq_zero` は `IsDomain` が要るので
  使えず、「`IsUnit (a - b)` から直交性」という現状の書き方が妥当。
- 自明な指標の射影は `GroupAlgebra.average`。指標で捻った版は Mathlib にない。冪等元の像の擬同型は既に `quasiIso_of_retractArrow` を使っている。

#### 4.4.3 一本化

- `positive`・`negative` を対で書いた補題（naturality・ImageMap・ShortComplex・BaseChangeIso・TensorIso・class）は、射影 e についての
  CochainIdempotent 版の補題を直接使えば各 1 本。
- InvolutionTensor の直交性 4 補題は `CochainIdempotent.tensor` の直交性 1 本に。
- 二項和（Involution 側の `orthogonalSum`）と有限和（Cubic 側の `imageFiniteSumIso`）の二重は有限和に揃え、二項は `Fin 2` で代用。
- CubicActionIdentityClass は ScalarClass の j = 0 版を 7 本並べただけ。`weightedK0Class_of_map_eq_id` 1 本を残す。
- InvolutionClassAcyclic・InvolutionClassShortExact は §4.4.5 の重み付き類に吸収。
- `change`・`rw` を長く連ねた証明（`positive_tensor_map` など）は `End` 環での `module`・`noncomm_ring` で短く。

#### 4.4.4 未使用

- CubicFourierTransform・CubicFourierEigen 全体（§4.4.1 の注意つき）、CubicFourierMinorIdentities の `cubicFourierMinor_difference_product`・
  `cubicFourierDeterminant_normalized`、CubicActionIdentityClass の 6 本、`characterShortComplex`・`_shortExact`、`tensorCharacterDecompositionIso`、
  `characterBaseChangeIso_hom_inclusion`。Involution 側：`positiveShortComplex`・`negativeShortComplex` と `_shortExact` 4 本、
  `positive/negativeBaseChangeIso_hom_inclusion`、`positive/negativeTensorIso_hom_inclusion`、`positivePositive` ほか 4 本の abbrev、
  `positiveClass`・`negativeClass`（自ファイル内だけ）。IdempotentTensor の `tensor_image_perfect`・`tensor_image_support`。
- `@[simp]` の `scalar_map` は参照 0 だが simp 集合が変わるのでビルドで確認。`CochainCubicAction.ext` は KoszulCubeFourierModelClass が使うので残す。
  `comapIso`・`comapIso_hom` は `scripts/audit_adams_action_transport.lean` が名前を書いているので残す（§6.4.4 では KT3 の削除で
  利用者がいなくなるとしているので、その時点で監査と合わせて判断）。

#### 4.4.5 位数 n の作用への一般化（§6.5 と共通）

involution（n = 2、固有値 ±1）と cubic action（n = 3、固有値 1・t・t²）は、射影の定義、冪等性、`e ≫ τ = ζ • e`、自然性、直交性、和が 1、
分解の同型、底変換、短完全列、非輪状、擬同型不変、テンソル積の分解、K₀ 類の積公式を一から別々に書いている。`positiveMap = ½(1 + τ)` は
`projectorMap a = ⅓(1 + a²τ + aτ²)` の n = 2 版、`InvolutionClass.k0Class = [正] − [負]` は `weightedK0Class` で E = ℤ・ζ = −1 とした
もの、`InvolutionTensorClass.k0Class_tensor` は `weightedK0Class_tensor` の n = 2 版。

一般形は 3 層：

1. 環の層（CommutativeAlgebra か RingTheory。提出候補）：R 代数 A の元 u で uⁿ = 1、`[Invertible (n : R)]`、ζ について
   `∀ k, 0 < k < n → IsUnit (1 − ζ^k)` のもとで、`eigenProjector u ζ j := ⅟n • Σ_{k<n} ζ^{−jk} • u^k` が
   `CompleteOrthogonalIdempotents` で、`u * e_j = ζ^j • e_j`、可換な u, v について `e_l(u ⊗ v) = Σ_i e_i(u) ⊗ e_{l−i}(v)`。
   §6.3.3 の Lagrange 射影子の一般化と同じもの。A = End K に適用すれば射影子の補題が一括で出る。
2. 複体の作用の層（Eigen/Cyclic）：`structure CochainCyclicAction (n) K where map; pow_eq : map ^ n = 1`。CochainInvolution（n = 2、ζ = −1）と
   CochainCubicAction（n = 3）は `abbrev` で残す（参照は CochainCubicAction が KTheory 38・PC 125、CochainInvolution が KTheory 23・PC 93）。
   `characterProjector`・`decompositionIso`・`baseChange`・`comapIso`・`tensor`・`biprod`・`scalar` をここに置く。
3. K₀ 類の層（Eigen/Class）：冪等元の族 e と重み w について `weightedK0Class e w := Σ_i w i ⊗ [im e_i]`。加法性・非輪状なら 0・同変な
   準同型で不変・二項和・スカラー作用・テンソル積の公式をそれぞれ 1 本で示す。

群内で 600〜800 行の削減が見込める。AntiEquivariance（±1 固有空間を入れ替える作用素）は n = 2 固有で利用 1 箇所なので n = 2 のまま残す。

#### 4.4.6 提出候補

1. 可換環 R 上、位数が R で可逆な有限アーベル群 G と指標 ψ について、指標冪等元 `e_ψ = |G|⁻¹ Σ_g ψ(g)⁻¹ g ∈ R[G]` が冪等で、
   指標値の差が単元なら `CompleteOrthogonalIdempotents`（`GroupAlgebra.average` の一般化、`IsDomain` を仮定しない）。
2. uⁿ = 1 の元の固有射影の多項式表示（1 の G = ZMod n の像）。
3. `map_invOf` の `OfNat` 版。

#### 4.4.7 リスク

- 層の逆転：CubicActionClass が `KTheory.SupportedCoefficients` を import している（PerfectComplex が KTheory に依存）。§6.2.5 と
  合わせて、PerfectComplex と KTheory のどちらを上の層にするかを決める（§4.5）。
- `set_option backward.isDefEq.respectTransparency false`・`backward.defeqAttrib.useBackward true` はファイルごとに付いている。統合時は
  `section` で範囲を限る。

### 4.5 順序の案と PerfectComplex・KTheory の境界

#### 4.5.1 層の境界

現状、PerfectComplex と KTheory は互いに依存している：PerfectComplex の IntegerEuler・IntegerEulerIso・CoefficientEuler・TensorTorComparison・
CubicActionClass が KTheory（HomologyEulerBasic・SupportedCoefficients）を import し、KTheory は PerfectComplex の K0WithSupport・閉台・
完全複体を使う。第4章と第6章を合わせた案：

- PerfectComplex を下の層にする。KTheory が持つ `PerfectModuleResolution`・`K0WithSupport.mk_shift` を PerfectComplex へ（§6.2.5）。
- PerfectComplex の IntegerEuler 系・namespace `Adams` の Koszul（KoszulOneModel・KoszulTensor・KoszulClasses）・FiniteProjectiveResolutions を
  KTheory へ（§4.2.1）。
- CubicActionClass が使う係数（`SupportedCoefficients`）は KTheory の軽い `Coefficients` に分けてあるので（§6.2.1）、
  係数の定義を PerfectComplex 側（ClosedSupport/K0 の隣）へ下ろすか、Eigen/CubicClass を KTheory に上げる。

#### 4.5.2 順序

1. 削除だけで済むもの：互換スタブ・互換 import（PC1 の 4 本、PC2 の 21 本、PC3 の 8 本）、確実な未使用。BS の再ビルドは起きない。
2. PC3 と KTheory の KT2・KT3 の小さな一本化（射影 e の一般補題の 2 回適用化、Positive・Negative の ε 化、Fourier 座標、`kernel.map`）。
3. §4.5.1 の層の境界の整理（PerfectComplex・KTheory の間のファイルの移動）。
4. PC1 の統合（CLMST の 27 モジュールが再ビルドになる正規化長さの移動は、CommutativeAlgebra の E・D と同じ時期にまとめる）。
5. 位数 n の作用・n 重テンソルへの一般化（§4.4.5、§6.5）と、HomologicalAlgebra の CochainTensor の Mathlib 化（§4.3.2）。
   最も大きい工事なので、1〜4 の後に費用対効果を見て判断する。
6. K₀ のモデルの一本化（§4.2.3。Inputs の引用の文言に関わるので計画判断が要る）。

## 第5章 LengthAlgebra・IntersectionMultiplicity

### 5.1 中身と外への影響

- **LengthAlgebra（LA）**：正規化された長さ λ（`NormalizedLength`、定義は PerfectComplex/NormalizedLength）の理論。Serre 商、almost 長さ、
  商の長さの評価、Koszul・錐・完全複体の λ-Euler 標数、根の塔の長さ（RootTowerLength/）。
- **IntersectionMultiplicity（IM）**：Serre の `chi` とその基本 API（同値・可換性・加法性・基底変換・dévissage・有限拡大・分解による評価）、
  Adams 作用による消滅、等標数 0 の対角環による正値性、パラメータ商の Tor。
- **BS は LA・IM を import しない。** CLMST は LA を多く import する（AlmostBaseChange・AlmostQuotientAction・AlmostVanishing・
  CyclicPowerReduction・GeometricDecay・QuotientPowerBound・Koszul{CokernelBounds,ErrorEuler,EulerComparison,EulerZero,Restriction,
  ZeroMonotonicity}・RootTowerLength/{CompletedNormalized,CompletedFiniteLength,CompletedQuotientEvaluation,CompletedTensorEvaluation,
  CoordinateModuleVanishing,CoordinateVanishing,StageDecay}。import なしで名前を使うもの：ShortExactEuler・HomologyExactBounds・
  ConeCompositionEuler・ConeHomologyLength）。これらは名前を残し、CLMST の import 行を書き換える。IM の利用者は Paper・Inputs・Asymptotic・
  CommutativeAlgebra/Koszul/RegularEuler・PerfectComplex/TensorTorComparison（BS/CLMST なし）。

### 5.2 層の問題（最初に解く）

1. **LA と PerfectComplex が入り組んでいる**：PC/NormalizedEuler が LA.ExactSequenceEuler を import し、それが LA.SerreQuotient を経て
   PC.NormalizedLength を import する。PC/KoszulLengthBounds は LA.HomologyExactBounds を import する。一方で LA の大半は PC/NormalizedEuler を
   import する。→ PC/NormalizedLength と LA の Serre 商の核（SerreQuotient・ExactSequenceEuler・ShortExactEuler・HomologyExactBounds）を
   一つの低い層（例 `LengthAlgebra/Core`、または PerfectComplex の下の `NormalizedLength/`）にまとめ、PC/NormalizedEuler はその上に置く。
2. **CA/Koszul/RegularEuler → IM.ResolutionEvaluation**（B2 で作ったファイル）：`koszulEulerChar_eq_chi`・
   `chi_eq_finrank_mul_length_of_resolution` を使う。ResolutionEvaluation の前半（60–280 行、`chiLam`・`chiOrd`・ひねりの補題）は
   PerfectComplex の内容なので PerfectComplex へ移し、`chi` の部分だけを IM に残す。そのうえで RegularEuler を IM の上へ上げるか、使う 2 補題を下ろす。
3. **PC/TensorTorComparison → IM.Basic**（`chiOrd_tensorResolution`）：`chi`（Basic、50 行）を HomologicalAlgebra/Tor の近くへ下ろせば解消。
4. **CA/KoszulMultiplicity/Formula → LA.ConeCompositionEuler**（`lambdaEuler_scalarCone_pow`）：ConeCompositionEuler を Core 側へ。
5. LA/Flat → IM.NormalizedTor、IM/ParameterQuotientTorBound → LA.PerfectVanishing：NormalizedTor（λ 長さの Tor）は LA へ移す。
6. `Inputs/IntersectionTheory` は包み：`Inputs.regularResolution` は `SerrePositivity.regularResolution`、`Inputs.intersectionVanishing` は
   `intersectionVanishing_of_adams` の重複。インライン化し、IM/Additivity・FiniteExtension の import を張り替える。

### 5.3 LA の統合（58 → 約 14 ファイル）

| 新しいファイル | 元のファイル |
| --- | --- |
| Core（低い層、§5.2 の 1） | SerreQuotient・ExactSequenceEuler・ShortExactEuler・HomologyExactBounds（＋PC/NormalizedLength を合わせる案） |
| Almost | AlmostQuotient・AlmostBaseChange・AlmostQuotientAction・AlmostVanishing・CyclicPowerReduction（CLMST が使う） |
| QuotientBounds | GeometricDecay・QuotientPowerBound・QuotientBounds・FinitelyGeneratedFiniteLength・Nontrivial |
| Cone | ConeHomologyLength・ConeCompositionEuler・KoszulHomologyLength |
| KoszulModule | KoszulCokernelBounds・KoszulErrorEuler・KoszulEulerComparison・KoszulEulerZero・KoszulRestriction・KoszulZeroMonotonicity（CLMST が使う） |
| Koszul | Koszul・Ordinary・OrdinaryKoszulEuler・Comparison・KoszulFormula |
| Perfect | PerfectHomology・PerfectVanishing・PerfectBaseChange |
| Flat | Flat・CohenMacaulay、IM の NormalizedTor |
| RootTowerLength/Basic | Defs・FiniteStage・FiniteGeneration |
| RootTowerLength/Additivity | AdditivityApproximation・AdditivityFinite・AdditivityFinitelyGenerated・Normalized |
| RootTowerLength/Completion | Completion・Completed*（CLMST が使う） |
| RootTowerLength/Coordinate | Coordinate*（CLMST が使う） |

- StageDecay は `stageRank` についての ENNReal の計算だけで RootTower.Basic しか import しない → CommutativeAlgebra/RootTower へ（CLMST が使う）。
- 名前空間が `LengthAlgebra`・`SerrePositivity`・`NormalizedLength`・`RootTowerLength`・`Section2`（論文の節の名前、RootTowerLength の
  Defs・FiniteStage・FiniteGeneration・Additivity*・Completion）と混在。`LengthAlgebra` と `LengthAlgebra.RootTower` にそろえる
  （CLMST が使う名前は参照の書き換えで追う）。
- 再エクスポートだけのファイル：LA/Foundations（importer はルートだけ）、HomologicalAlgebra/KoszulHomologyLength（LA.KoszulHomologyLength の
  再エクスポート）。どちらも削除。

### 5.4 IM の統合（21 → 約 7 ファイル）

| 新しいファイル | 元のファイル |
| --- | --- |
| Basic | Basic・Equivalence・BaseChange（§5.2 の 3 で `chi` を下ろすなら HomologicalAlgebra/Tor 側へ） |
| Additivity | Additivity・Devissage・FiniteExtension |
| Vanishing | AdamsVanishing・AdamsVanishingTwo・AdamsVanishingThree・AdamsVanishingAll・CubicCyclotomicBaseChange（一本の鎖、約 200 行） |
| EqualCharZero/Ring | DiagonalRing・DiagonalFlat |
| EqualCharZero/Tor | DiagonalTor・DiagonalDimension |
| EqualCharZero/Positivity | DiagonalPositivity・EqualCharZeroPositivity |
| ParameterQuotient | ParameterQuotientTor・ParameterQuotientTorBound |
| ResolutionEvaluation | `chi` の部分（280–488 行）だけ。前半は PerfectComplex へ（§5.2 の 2） |

### 5.5 死んだファイル・未使用

- **LA の死んだ連鎖（約 880 行）**：Foundations（再エクスポート）、EulerCompatibility（外の利用なし）、FlatRealization（3 定理とも未使用。
  Paper/Section4/FlatRealization は import するが LA.Flat しか使わない）、それだけが使う PerfectMinimalLowerBound → PerfectLowerBound →
  PerfectHomologyComparison → FiniteQuotientEquivalence → FiniteQuotientComparison。生きている版は PerfectComplex/MinimalLowerBound・
  Asymptotic/PaperMinimalLowerBound・Paper/Section4/FlatRealization。PerfectVanishing は Asymptotic/RankVanishing と ParameterQuotientTorBound
  が使うので残す。
- **AlmostFactorQuotient**：importer なし。`scripts/audit_clmst.lean` だけが import して 2 定理を確かめている。監査の行と一緒に削除。
- 未使用の宣言：IM の `quotDiagEquiv_mk`（simp）・`fwd_tmul`。LA の `length_eq_of_full_almost_iso`、CohenMacaulay の `koszulFinite_of_cm`・
  `koszulEuler_of_cm`・`tor_length_of_cm`（使われているのは `koszulAcyclic_of_cm` だけ）、`flat_rank_iff_koszul`、`perfectBaseChangeHomology`、
  `perfectEuler_triangle`、`towerLengthFun_eq_iSup_of_directed_union`、`towerLengthFun_add_of_exact_of_finitelyGeneratedExact`、
  `tower_baseChange_shortExact`、`towerLengthFun_add_of_exact_finitePresentation`、`completedNormalizedLength_restrictScalars`、
  `coordinateZeroExponent_at`（simp）、`presentedLength_congr`、`subsingleton_tensorProduct_of_right`、`finiteLengthQuotient_isZero_iff`、
  `extendedQuotientLength_obj`（simp）。
- ファイルの中だけで使われている約 120 の名前は private に（ParameterQuotientTor 23、DiagonalDimension 14、RootTowerLength/FiniteStage 14、
  DiagonalTor 11、DiagonalRing 9、FiniteExtension 7 など）。

### 5.6 Mathlib との重なり

- Mathlib には交点重複度・Serre の Tor 公式・Koszul 複体・長さで値を取る Euler 標数がない。`HomologicalComplex.eulerChar` は finrank 版で代わりにならない。
- `quotEquivOfKerEq` は `Submodule.quotEquivOfEq ≪≫ quotKerEquivOfSurjective`（確度高、インライン化）。
- `isUnit_two_of_residue_ne_zero` は `IsLocalRing.residue_ne_zero_iff_isUnit` から直接（確度高）。
- `subsingleton_tensorProduct_of_right`（RootTowerLength/Defs）は `inferInstance`（確度高、削除）。
- `tensorQuotQuotEquiv`（A/I ⊗ A/J ≃ A/(I⊔J)）は `TensorProduct.quotientTensorQuotientEquiv` と商の同一視の合成（確度中）。
- 通常の長さの加法性は `Module.length_eq_add_of_exact`（`module_length_add` は λ 版なので別）。

### 5.7 一本化

- **Euler 標数の種類**：`chi`（IM、ℤ、Tor）、`chiOrd`・`chiLam`（PC/Basic）、`lambdaEuler`（PC/NormalizedEuler）、`perfectEuler`（LA/PerfectHomology）、
  `koszulEuler`（LA/Koszul）、`koszulEulerChar`（CA/Koszul.lean）、`homologyLengthSum`（CA/Length/Euler）。橋渡しの補題が散らばっている：
  `ordinary_koszulEuler_eq_koszulEulerChar`（LA/OrdinaryKoszulEuler）、`koszulEulerChar_self`・`koszulEulerChar_eq_chiOrd_of_residue_surjective`
  （CA/KoszulMultiplicity/Formula）、`koszulEulerChar_eq_chi`（IM/ResolutionEvaluation）、`chiOrd_eq_alternating_term_lengths`（CA/Length/Euler）。
  → 比較のファイル 1 本（層の順で一番上に置ける場所、例 `LengthAlgebra/EulerComparison`）に集める。定義の種類を減らせるかは PerfectComplex の
  計画と合わせて検討する。
- `isFiniteLength_torModule_of_finite_free_left`・`chi_of_finite_free_left`（ResolutionEvaluation）は `length_tensorProduct_of_finite_free_left`
  （CA/Length/Basic）と並行。
- `torModule_eventually_subsingleton`（IM/Additivity）は Inputs/IntersectionTheory・HomologicalAlgebra/TorFiniteLength の Tor の消滅と重なる。
- LA の almost 長さ（Almost*）は CommutativeAlgebra/Almost/SerreComparison・CLMST/AlmostLength・NormalizedAlmostLength と並行。第8章
  （第8章）で CLMST 側の特殊化を LA へ寄せる。
- `chi_rank_factor_{left,right}_of_additivity_and_vanishing` は 3 つの等式を仮定に取って書き換えるだけ。インライン化。

### 5.8 その他

- FiniteExtension の docstring が「Inputs の名前付きの未証明定理」と書いているが、今は `intersectionVanishing_of_adams` で証明済み。直す。
- 一般的すぎる名前：`SerrePositivity.chi`、`ParamQuot.{B, IC, U, T1, T2, fwd, bwd, ψ}`、`TorBound.Kills`、`TorClaim`、`module_length_add`、
  `koszulScalars`、`DiagonalRing.{eval, var, const, diag}`。
- IM の Adams のファイルは英語の docstring、他は日本語。統合のときに日本語の形式（概要・方針・規約・使われ方）にそろえる。
- `backward.isDefEq.respectTransparency false` が約 20 ファイル、`backward.defeqAttrib.useBackward true` が IM の Adams・FiniteQuotientEquivalence・
  CubicCyclotomicBaseChange に。統合のときに外せるか試す。

#### 提出候補

Serre の交点重複度 `chi`（`chi_eq_sum_range`、`chi_congr`・`chi_comm`、各変数での加法性、平坦な局所基底変換）、`IsLocalHom (MvPowerSeries.C)`、
`tensorQuotQuotEquiv`（Mathlib の合成がなければ）、`sum_Icc_negOnePow_eq_sum_range`、ENNReal の幾何的な減衰（`ennreal_eq_zero_of_geometric_bound`、
一般的な名前のまま ENNReal のファイルへ）、`radical_eq_maximalIdeal_of_length_ne_top`。

### 5.9 順序

1. 死んだ連鎖・未使用・再エクスポートの削除、確度高の Mathlib への置き換え（CLMST の参照なし）。
2. 層の問題（§5.2）。PerfectComplex の PC1（Basic・NormalizedLength）と同じ全依存ビルドにまとめる。
3. 統合（§5.3・§5.4）。CLMST が import する LA のファイルの移動は import 行の書き換えだけで済む（許可済みの範囲）。
4. Euler 標数の比較の一本化（§5.7）。

## 第6章 KTheory

### 6.1 群の分け方と外への影響

| 群 | 内容 | ファイル数 |
| --- | --- | --- |
| KT1 | トップ階層：G₀・K₀ の局所化、dévissage、係数の延長、台付き加群、格子、極大台の長さ | 40 |
| KT2 | Adams/ の基礎：weight 分解、Lagrange 射影子、cyclic 2・3、Koszul の明示モデル | 67 |
| KT3 | Adams/ の tensor square・tensor cube | 44 |

- BhattScholze・CLMST は KTheory を import せず、宣言の参照もない（KT2・KT3 で確認）。改名の波及は KTheory の中と
  IntersectionMultiplicity/AdamsVanishing{,Two,Three}、`SerrePositivity.lean`、生成される `scripts/audit/adams.lean` に限られる。
- Adams/ の外向きの公開面は、`cup_enlarge_eq_zero`、`cyclicTwoFamily`、`cyclicThreeFamily`、`CubicCoefficientField`・
  `cubicCoefficientRoot*` のほぼ 4 点。

### 6.2 KT1 トップ階層（G₀・K₀ の局所化、dévissage、係数、格子、極大台）

規模：40 ファイル、3618 行（最大は G0Localization の 216 行）。主な利用者は KTheory/Adams（約 30 ファイル）、PerfectComplex の 4 本
（IntegerEuler・TensorTorComparison・CoefficientEuler・CubicActionClass が KTheory を import する）、InfinityCategories/Derived/SupportK0、
IntersectionMultiplicity/AdamsVanishing。SupportedModule の下流は 74 モジュール（Paper 13、IntersectionMultiplicity 8 など。BS は含まない）。

#### 6.2.1 統合（40 → 12 ファイル）

| 新しいファイル | 元のファイル |
| --- | --- |
| G0/Basic（約 330 行） | SupportedModule・G0Supported・SupportedExactEuler の `image`・`coimage`・`mk_of_isZero`・CA の SubmoduleExact |
| G0/Functoriality（約 200 行） | G0Functoriality・G0Torsion の `localize_mk_eq_zero` |
| G0/Lattice（約 280 行） | SupportedLattice・LatticeClass・LatticeExact |
| G0/Localization（約 400 行） | G0Torsion・TorsionAnnihilator・G0Localization・LocalizationKernelSupport |
| G0/MaximalSupport（約 380 行） | MaximalSupportModules・MaximalSupportLength・MaximalSupportLocalLength・MaximalSupportLengthEquiv・Adams の MaximalSupportModules・MaximalLengthEvaluation・MaximalLengthEquiv |
| G0/SemilocalSupport（約 330 行） | CA の SupportHeight・SemilocalSupport・ModuleSupportHeight（第2章で KTheory に回したものの受け入れ先。Adams の再エクスポート 2 本は削除、SupportHeight の未使用 3 宣言は移動時に削除） |
| Comparison/ResolutionClass（約 200 行） | ResolutionClass・ResolutionAdditivity |
| Comparison/HomologyEuler（軽量） | SupportedExactEuler の Euler 部分・HomologyEulerBasic（PerfectComplex/IntegerEuler が import するので重い比較と分ける） |
| Comparison/Basic（約 470 行） | HomologyEuler・HomologyPeeling・ComparisonInverse・ComparisonNaturality |
| K0Localization | K0Localization |
| Coefficients（軽量） | G0Coefficients・SupportedCoefficients（PerfectComplex の CoefficientEuler・CubicActionClass が import するので軽く保つ） |
| LocalizationCoefficients | LocalizationCoefficients・K0LocalizationCoefficients・MaximalSupportCoefficientLength |

- 削除：再エクスポートの ModuleClosedSupport（4 行。TensorTorComparison は CA の ModuleClosedSupport を直接 import）・LocalizedResolution（10 行）。
  CoefficientExtension・CoefficientExactness・CoefficientLinearExtension は Mathlib に置き換え、残り（`coefficientPairing`）を LinearAlgebra へ。
- dévissage 一式（Devissage* 7 ファイル、654 行）：利用者がいない（`g0QuotientDevissageEquiv`・`G0` はどこからも使われない。
  Paper/Section5/ModuleReduction が使うのは別物の IntersectionMultiplicity/Devissage）。DevissageAnnihilated が不要な
  K0LocalizationCoefficients を import しているので依存グラフの最上段に載っている。論文の層から外す。**決定（2026-11-01、ユーザー）**：research/ へ退避する（ビルドの対象から外し、ファイルは残す）。区切り 1-4 で行う。
- 循環の前提：ComparisonNaturality → LocalizationCoefficients（不要）と DevissageAnnihilated → K0LocalizationCoefficients（偽の依存）の
  import を先に外す。ResolutionClass → G0Localization の LocalizedResolution 経由の依存も偽物。

- **CA から持ち越した移動（2026-10-30、B2 実施時）**：CA の SupportHeight・ModuleSupportHeight は B2 では動かさず、
  `CommutativeAlgebra/` に残した。受け入れ先の G0/SemilocalSupport がまだなく、KTheory の既存ファイルへ入れると
  CommutativeAlgebra（SemilocalSupport・ModuleSupportHeight 自身）が KTheory を import する層の逆転になるため。
  E の SemilocalSupport も同じ理由で KT1 まで動かさない。KT1 で G0/SemilocalSupport を作るときに 3 本をまとめて移す。
  今の import 元：`CommutativeAlgebra/SemilocalSupport`・`CommutativeAlgebra/ModuleSupportHeight`・
  `KTheory/Adams/SupportHeight`（再エクスポート、削除予定）・`IntersectionMultiplicity/AdamsVanishing`。
  移すときは IntersectionMultiplicity → KTheory の向きになるので、AdamsVanishing の閉包が増えないかを確かめる。

#### 6.2.2 Mathlib との重なり（固定版と最新版で差なし）

- 確度高：`g0CoefficientMap E f` は定義が `f.toIntLinearMap.baseChange E` そのもの（`_tmul`・`_comp`・`_id` は `LinearMap.baseChange_tmul`・
  `_comp`・`_id`）。`coefficientLinearExtension E f` → `f.toIntLinearMap.liftBaseChange E`、`coefficientLinearMap_ext` →
  `LinearMap.liftBaseChangeEquiv` の単射性。`idealAnnihilatorTorsion` → `Module.isTorsionBySet_iff_subset_annihilator`。
  `annihilator_le_of_injective`・`_surjective` → Mathlib の `LinearMap.annihilator_le_of_*`。`LinearMap.exact_iff.mpr (by rw [ker_mkQ, range_subtype])`
  の 3 箇所 → `LinearMap.exact_subtype_mkQ`。`localizedModuleTensorEquiv` → `LocalizedModule.equivTensorProduct`（未使用なので削除）。
  `coefficientField_flat` は `inferInstance` だけなので削除。
- 確度中：`moduleSupport_extendScalars` → `Module.support_subset_preimage_comap`。`g0CoefficientMap_ker_eq_range` は `lTensor_exact` の包み。
  `maximalSupportLengthMap` の加法性 → `Module.length_eq_add_of_exact`。
- Mathlib にないもの：完全列による K₀（G₀）。Mathlib の Grothendieck 群はモノイドの群完備化だけ。使える基盤は `ObjectProperty.IsSerreClass`、
  `IsFiniteLength`、`IsLocalizedModule`、Serre 商の局所化。
- 第2章（E 群）で `IsModuleSTorsion` を `Module.IsTorsion'` に置き換えると、G0Torsion・TorsionAnnihilator・LatticeClass・G0Localization・
  LocalizationKernelSupport が波及を受ける。

#### 6.2.3 一本化

- 局所化完全列が G0・K0 × ℤ・係数 E の 2×2 に 3 版を加えた形で重複（`localize_surjective`・`localize_kernel_supported`・
  `localize_enlarge_principal_eq_zero`・`localize_away_kernel_range`）。閉台の族に `enlarge` と `localize` を持たせた構造と、
  「自然同型に沿って核と右完全性を移す」「核が `enlarge` の像の有向合併という性質は `baseChange E` で保たれる」の 2 つの汎用補題を置けば、
  K0 版と係数版は系になる（約 200 行減）。
- `enlarge` 版と `map` 版の自然性が二重（`resClass_*`・`resolutionMap_*`・`homologyEuler_*`）。逆写像に沿って可換図式を移す補題一つか、
  `enlarge` を `map (RingHom.id)` の特殊例にする。
- 係数版の定義（G0 と K0 の `coefficientEnlarge`・`coefficientLocalize`・`coefficientMap` など）はすべて `baseChange` の別名。Adams が
  多用する（`Coefficients` 57 箇所、`coefficientEnlarge` 24 箇所）ので名前は `abbrev` で残し、別名と補題は Mathlib に寄せる。
- Euler 加法性が CategoryTheory と二重実装（`SupportedExactEuler.mk_exact_images` ↔ `ExactSequenceEuler.additiveLength_exact_images`、
  `supportedHomologyEuler_*` ↔ `HomologicalEuler.homologicalEuler_*`、`K0WithSupport.homologyEuler` ↔ `homologicalEulerK0`）。値域を任意の
  `AddCommGroup` にし、評価を `IsSerreClass` な部分圏上の関数とした `homologicalEulerK0` 一本にすれば、G0 版はその普遍例、ℝ 版と
  IntegerEuler はその合成になる。
- 部分加群・商の短完全列を 6 回、制限の短完全列を 2 回組み立てている → `SupportedModuleShortExact.ofSubmodule`・`restrict` の一般の def に。
- 「台 ⊆ V(J) から annihilator の冪を得る」が 5 箇所 → CA に「有限加群で Module.support ⊆ V(J) ↔ J ≤ √ann、∃ n, J^n ≤ ann」を置く。
- `HasPrincipalLocalizationSupport` と `HasPrincipalCoefficientSupport` は同じ述語。CA/PrincipalSupport の隣に一本化。
- `K0WithSupport.localize` の第 1 引数は未使用。K0Localization の `[IsNoetherianRing S] [HasFiniteProjectiveResolutions S]` は局所化から
  導けるので、主補題から外せば `_of_resolution_contract` の 3 版が消える（Adams が使うのは 1 つだけ）。

#### 6.2.4 未使用

- dévissage 一式（§6.2.1）。
- 個別：`coefficientLinearExtension_unique`、`k0Class_eq_sum_resolutionClasses`、`PerfectModuleResolution.exists_homotopyEquiv`
  （PerfectComplex 側に置けば使い道あり）、`directSum`・`directSumShortExact`・`mk_directSum`（`@[simp]`）、`G0WithSupport.mk_zero`（`@[simp]`）、
  `finiteModuleSupportedOn.top_iff`、`supportedFGModuleOnObj`、`localizedModuleTensorEquiv`、`coefficientField_flat`、
  `coefficientLocalize_ker_range`、`coefficientTorsionInclusion_injective`、`eq_sum_localLengthMap`、`coefficientCup_enlarge`・
  `coefficientCup_map`（基底変換との両立として残す価値あり）、`localize_surjective_of_resolution_contract`、
  `localize_kernel_supported_of_resolution_contract`、`G0WithSupport.enlarge_map`。
- 内部だけで使うもの（private 化）：`principalLocalizationSupportSubgroup`、`exists_supported_lattice`、`coefficientEnlarge_refl`、
  `mk_complex_shift`。instance `sourceLocalizationMap_isLocalizedModule` は暗黙に使われているので残す。

#### 6.2.5 外へ回すもの

- PerfectComplex へ：`PerfectModuleResolution` 本体と `augmentation`・`exists_comparison`・`comparison_quasiIso`・`support`・`baseChange`・
  `mappingCone`、`hasFiniteProjectiveResolutions_of_localization`、`K0WithSupport.mk_shift`・`mk_complex_shift`（`K0WithSupport` は
  PerfectComplex/ClosedSupportK0 で定義）。逆向きに第4章は IntegerEuler 系・Adams の Koszul・FiniteProjectiveResolutions を
  KTheory へ回す（§4.2.1）。どちらを KTheory の上の層とするかは第4章と合わせて決める。
- HomologicalAlgebra へ：`exists_topHomologyMap`。
- CommutativeAlgebra（Support）へ：`moduleSupport_extendScalars`、`exists_pow_annihilator_of_support`（局所化版も）、
  `moduleSTorsion_of_support_principal`、`quotientModule_annihilator`、`maximalSupport_pullback_le`。
- CategoryTheory へ：Euler の汎用部分。LinearAlgebra へ：`coefficientPairing`・`integerPairing`（引数の型が異なる双線形写像の基底変換）。

#### 6.2.6 提出候補

- 拡大で閉じた ObjectProperty（小さいアーベル圏）の完全列 K₀ と API（`mk`・`lift`・`hom_ext`・`mk_shortExact`、Euler 加法性、完全関手の誘導写像）。
  `G0WithSupport Z` はその特殊例。`finiteModuleSupportedOn Z` の `IsSerreClass` インスタンス。
- 一般形の dévissage、有限長の加群の K₀ は単純加群の同型類上の自由群、K₀ の局所化完全列（Mathlib の SerreClass/Localization と接続）。
- `ModuleCat (R⧸J) ≌ {M | J ≤ ann M}`、`LinearMap.baseChange₂`、台の小さな補題。

#### 6.2.7 リスク

- BS/CLMST への波及はない。
- 監査：`scripts/audit_euler_group_shared.lean`（`G0WithSupport.mk_exact_images`・`supportedModuleEuler_exact_sequence`・
  `supportedHomologyEuler_triangle`）、`scripts/audit_triangulated_k0_shift_shared.lean`（ResolutionClass と `K0WithSupport.mk_shift`）を手で直す。
- Comparison/HomologyEuler を重い比較と統合すると PerfectComplex/IntegerEuler の閉包が 49 から約 110 に増えるので分ける。

### 6.3 KT2 Adams の基礎

規模：67 ファイル、5909 行。weight 層（約 900 行）、cyclic 2（約 700 行）、cyclic 3（約 450 行）、Koszul の明示モデル（約 3800 行、
うち KoszulCube* が 19 ファイル約 2650 行）。

#### 6.3.1 統合（67 → 10 ファイル、KTheory/Adams/ のまま）

| 新しいファイル | 元のファイル |
| --- | --- |
| Weight（約 300 行） | WeightPolynomial・LagrangeProjectors・WeightOperators・PolynomialNaturality・WeightProduct |
| Family（約 100 行） | Family |
| PureWeight（約 600 行） | IteratedPrimeLocalization・MaximalPureWeight・CoefficientLengthEquiv・MaximalLengthEquiv・MaximalSupportModules・SemilocalPureWeight・WeightDefectLift・WeightAnnihilation・WeightDecomposition・CupVanishing |
| CyclicTwo（約 450 行） | CyclicTwo・SupportNaturality・BaseChangeNaturality・UnitNormalization・KoszulNormalization・CyclicTwoFamily |
| CyclicThree（約 450 行） | CyclicThree・CubicSupportNaturality・CubicBaseChangeNaturality・CubicUnitNormalization・CubicKoszulNormalization・CyclicThreeFamily・CubicCoefficientField |
| KoszulSquare（約 600 行） | KoszulSquareModel・KoszulSquareSwap・KoszulSquareCoordinates・KoszulSquareDual・KoszulShiftOneModel |
| KoszulSquareSplitting（約 570 行、一本化で約 300 行） | Koszul{Positive,Negative}{Embedding,Retraction} |
| KoszulCube（約 950 行） | KoszulCubeModel・KoszulCubeGenerators・KoszulCubeDifferential・KoszulCubeExt・KoszulCubeCoordinates |
| KoszulCubeFourier（約 1000 行） | KoszulCubeFourier{One,OneInverse,OneCoordinates,Two,TwoInverse,TwoCoordinates,Basis（hom_ext のみ）,Embeddings}・KoszulShiftTwoModel |
| KoszulCubeFourierModel（約 500 行） | KoszulCubeFourierModel{Map,Generators,Inverse,Iso,Class} |

- 削除するファイル：互換用に import だけをまとめた 7 本（SemilocalSupport・SupportHeight・KoszulOneBasis・KoszulOneModel・KoszulTensor・
  MaximalLengthEvaluation・Coefficients。importer は実体を直接 import する）、KoszulCubeBasis（全体が未使用）、KoszulShiftTwoClass
  （§6.3.2 の置き換えで消える）、KoszulSequenceNormalization（全体が未使用）。
- import の向きはほぼ一列（Weight → Family → PureWeight、CyclicTwo・CyclicThree ← KoszulSquare*・KoszulCube*）。KT3 との境界
  （KoszulSquareModel → TensorSquare、KoszulPositiveEmbedding → TensorSquareEigenspaces、BaseChangeNaturality →
  TensorSquareBaseChangeEigenspaces、CyclicThree → TensorCube*）は KT3 と同時に縮約して閉路を確かめる。
- KoszulCube* は `simp` の多い長い証明が集まるので、1 ファイルにせず 3 分割にしておく。

#### 6.3.2 Mathlib との重なり

- 確度高：`polynomial_on_eigenvector` = `Module.End.aeval_apply_of_mem_apply_eq_smul`（LinearAlgebra/Eigenspace/Minpoly.lean）。
  `endomorphism_pow_intertwine` → `Module.End.commute_pow_left_of_commute`。`coefficient_empty_zero` はプロジェクト内の
  `K0WithSupport.coefficient_eq_zero_of_empty_support` の包み。`oneKoszulShiftTwo_class` は `TriangulatedK0.mk_shift`（または
  `K0WithSupport.mk_shift`）と `oneKoszulClass` から出る。`oneKoszulShiftOne_class` は `oneKoszulClass_shift_one` の別名。
- 確度中：`cubicCoefficientRoot` は `.choose` で定義されている。`IsCyclotomicExtension.zeta 3 ℚ (CyclotomicField 3 ℚ)` と
  `zeta_spec` で def と補題に直す。
- Mathlib にないもの：Lagrange 射影子（Mathlib の固有分解は有限次元が前提）、`polynomial_intertwine`、Koszul 複体。

#### 6.3.3 一本化

- `cyclicTwo_koszul`（ℤ 版）は Family の一般補題 `SupportedAdams.koszul` の特殊例で未使用。`coefficientCyclicTwo_koszul`・
  `cyclicThree_koszul` も不要。
- Positive・Negative の 4 ファイルは、符号 ±、次数の位置、相手（`oneKoszulComplex (2a)` か `oneKoszulShiftOne a`）だけが違い、
  証明の骨格は同じ。符号 ε ∈ {±1} で添字付けた一本の補題にする。
- ShiftOneModel・ShiftTwoModel を `oneKoszulShift k` 一本に。
- KoszulCube の Fourier 側の 1 と 2 は、Coordinates・Inverse・Basis の 3 段で 9 項ずつの同じ手計算を繰り返している。
  PerfectComplex/CubicFourierTransform の行列 F と F⁻¹ = (1/3)F̄ を一度示し、「Fin 3 添字の biproduct ≅ Fin 3 → R」に通せば、
  約 500 行の座標補題が `Matrix` の計算に縮む。
- cyclic 2 と cyclic 3 の 6 対（SupportNaturality・BaseChangeNaturality・UnitNormalization・KoszulNormalization・Family・
  `algebraInvertible{Two,Three}`）は「代表元の水準の類が enlarge・map と可換なら `K0WithSupport.lift` も可換」の一本の補題で、
  各 10 行程度になる。`algebraInvertible{Two,Three}` は `Invertible (n : A)` の一般形に。
- `LagrangeProjectors` を「E 代数の元 T で ∏(T − v j) = 0 となるもの」に一般化する（証明はそのまま通る）。そうすれば PerfectComplex の
  `CochainInvolution.positiveMap`（(1+τ)/2）と `CochainCubicAction.projectorMap` が A = End(K) の場合として同じ補題から出る。

#### 6.3.4 未使用

- 確実に削除してよいもの：KoszulCubeBasis 全体（117 行）、KoszulCubeModel の `oneKoszulCubeX{Zero,NegOne,NegTwo,NegThree}Iso` と
  それだけが使う錐の同型 4 つ、KoszulCubeFourierBasis の `{One,Two,Top}BasisIso`（約 115 行、`_hom_ext` 3 本は残す）、
  KoszulSequenceNormalization 全体、`cyclicTwo_unique`、`cyclicThreeValue_unique`、`cyclicThree_unique`、
  `cyclicThreeValue_mk_concrete`、`cyclicThree_koszul`、`coefficientCyclicTwo_koszul`、`iteratedPrimeLocalizationEquiv`、
  `HeightAtLeast.semilocalLengthEquiv`、`HeightAtLeast.localized_module_finiteLength`、`weightPolynomial_top`、
  `SupportedAdams.weightProjector_enlarge`、`LocalizationAdamsFamily.weightProjector_idem`・`_orthogonal`（論文の weight 分解の
  完全な主張として残す選択肢あり）、`oneKoszul{Positive,Negative}Iso_hom_inclusion`、`oneKoszulTensorScalar_unitor`、
  `oneKoszulCubeGenerator_apply`、`cubicCoefficientRoot_primitive`。
- 残すもの：KoszulCubeFourier{One,Two}Coordinates の `@[simp]` 座標補題 18 本（`simp [ht]` が使う）、KoszulSquareDual の `@[simp]` 7 本
  （削除前にビルドで確認）、instance として使われる `oneKoszulCubeFourierModelMap_{f_,}isIso`。

#### 6.3.5 外へ回すもの

- CommutativeAlgebra へ：`iteratedPrime_regular_dimension`、`HeightAtLeast.*`。
- PerfectComplex の Koszul へ：`oneKoszulShift{One,Two}` の一般化、`scalarTensorDiagonal_*`、`scalarModule_braiding_id`、
  `tensorSquareUnit_swap`、`oneKoszulX{Zero,NegOne}_generator_d_apply`。
- KTheory/Coefficient* へ：`coefficientK0LengthEquiv`、`coefficient_eq_zero_of_localizations`（Adams に依存しない）。

#### 6.3.6 提出候補

- Lagrange 射影子一式（有限次元を仮定しない。Mathlib/LinearAlgebra/Lagrange.lean か Eigenspace/）。
- `polynomial_intertwine`（`Module.End.aeval_comp_of_comp_eq` のような名前で）。
- 無限次元の固有分解 `weightDecomposition` の抽象部分。
- 長期的には Koszul 複体（K(a) と、その n 重テンソル ≅ K(a,…,a)）。

### 6.4 KT3 tensor square・tensor cube

規模：44 ファイル、4235 行（TensorSquare* 15 本 1377 行、TensorCube* 29 本 2858 行）。`maxHeartbeats` の引き上げが cube 側に 18 箇所
（Exact・QuotientAction・HighMixedKernel に集中）。群の外の利用者は Adams/ の中だけ。

#### 6.4.1 統合（44 → 8 ファイル、3 ファイル削除）

| 新しいファイル | 元のファイル |
| --- | --- |
| TensorSquare（約 330 行） | TensorSquare・TensorSquareEigenspaces・TensorSquareMaps・TensorSquareBaseChange・TensorSquareBaseChangeEigenspaces・TensorSquareShuffle |
| TensorSquareFiltration（約 560 行） | TensorSquareFiltration・TensorSquareMixed・TensorSquareMixedSplitting・TensorSquareMixedCancellation |
| TensorSquareClass（約 230 行） | TensorSquareAdditivity・TensorSquareAcyclicClass・TensorSquareEvaluation・TensorSquareMultiplicativity |
| TensorCube（約 230 行） | TensorCube・TensorCubeEigenspaces（未使用分を除く）・TensorCubeMaps・TensorCubeBaseChangeEigenspaces・TensorCubeTensor |
| TensorCubeFiltration（約 500 行） | TensorCubeFiltration・TensorCubeFirstLayer・TensorCubeFirstLayerSplitting・TensorCubeSparsePartition |
| TensorCubeLowMixed（約 850 行、「成分と短完全性」と「回転と台」の二つに分けるのが安全） | LowMixed・LowMixedInclusions・LowMixedSections・LowMixedRotation・LowMixedReconstruction・LowMixedExact・LowMixedSupport |
| TensorCubeHighMixed（約 580 行） | HighMixed・HighMixedComponents・HighMixedSections・HighMixedEpi・HighMixedKernel・HighMixedQuotient（cokernel の部分を除く） |
| TensorCubeClass（約 300 行） | TensorCubeMixedCancellation・TensorCubeAdditivity・TensorCubeEvaluation・TensorCubeMultiplicativity |

- ファイルごと削除：TensorCube{Low,High}MixedQuotientAction、TensorSquareFiltrationImages（中身がすべて未使用）。
- 置き場所は `KTheory/Adams/TensorPower/` にまとめてもよい。import の向きは square が A → B → C、cube が D → E → {F,G} → H。
- `cyclicTwo_cup`・`cyclicThree_cup` は CyclicTwo・CyclicThree を import しているので、C・H に入れると循環する。CyclicTwo.lean・
  CyclicThree.lean へ移す（両者は「生成元 mk X, mk Q 上で cup と可換なら全体で可換」という K0WithSupport の一般補題にまとまる）。
- TensorCubeUnitRotation は CubicUnitNormalization へ。
- 変えない名前（群の外から参照）：tensorSquare(Swap/Map)、`ιTensorObj_tensorSquareSwap`、`tensorSquareClass`、
  `tensorSquare{Positive,Negative}(Projector,_map,_perfect,_support)`、`{Positive,Negative}BaseChangeIso`、
  `tensorSquareEvaluation(_iso,_triangle)`、`cyclicTwo_cup`、`tensorCube(Rotation,_perfect,_support,_apply_ι)`、`tensorCubeAction`、
  `tensorCubeClass`、`tensorCubeCharacterBaseChangeIso`、`tensorCubeEvaluation(_iso,_triangle)`、`cyclicThree_cup`、
  `tensorCubeUnit_rotation`、`tensorCubeUnitIso`。

#### 6.4.2 Mathlib との重なり

- `kernel.map` で置き換えられる（確度高）：`tensorSquareKernelSwap`、`tensorCubeKernelRotation`、`tensorCubeFirstLayerRotation`
  （同変な写像の核へ作用を制限する `kernel.lift` を手で書いたもの）。`_inclusion`・`_sq`・`_cube`・`*_FirstMap_rotation` は
  `kernel.lift_map`・`kernel.map_ι` 系にまとまる。
- `cochainBiprodX_hom_ext`・`cochainBiprodFstX`・`SndX`（TensorSquareMixedSplitting）は HomologicalAlgebra/CochainKernelLift の
  `cochainBiprodDegree_hom_ext` と同じ。どちらも Mathlib の `HomologicalComplex.biprodXIso` と `biprod.hom_ext` で書ける（確度中）。
- `tensorSquareMixedCokernelIso` は CategoryTheory/ShortExactCokernel の `shortExactCokernelIso` と同じだが、未使用なので削除。
- Mathlib にないもの：HomologicalComplex の braided・symmetric 構造、位数 n の作用による指標の射影子分解（`Action V G`、
  `Representation.averageMap`、`IsIdempotentComplete (HomologicalComplex C c)` はある）。

#### 6.4.3 一本化

- Evaluation の 2 ファイルは同じ形。square 側の擬同型不変性を正・負の像ごとに手で示しているのをやめ、PerfectComplex に
  `CochainInvolution.k0Class_eq_of_quasiIso` を足せば TensorSquareMaps はほぼ消える。さらに「擬同型で不変で短完全列に加法的な類関数から
  評価を作る」一般構成を一つ置けば、両方の Evaluation が数行になる（BaseChangeNaturality・SupportNaturality の代表元の取り回しも同じ）。
- `tensorSquareMap_{epi,mono}_of_shortExact` と cube 版は「各次数が射影的なら q^{⊗n} も epi（f^{⊗n} も mono）」の一般補題一本から。
- Splitting の組み立て（square の MixedSplitting と cube の LowMixedExact）は、値域が k 成分の biproduct のときの一般補題に。
- 短完全性の示し方が三通り（square と cube low は各次数の分裂、cube high は epi と核の同定）。high も分裂に揃えると HighMixedKernel
  （約 110 行）が要らなくなる見込み（確度中）。
- 0/1/2 の成分の三重化（HighMixed・LowMixed・Projection・Section・component の 0/1/2）：入れ子の ⊞ を `⨁ j : Fin 3` にし、成分 j を
  成分 0 を rotation^j で輸送したものと定義すれば、j について一度だけ書ける（Sections・Inclusions・Epi で約 700 行の半分以上が減る）。

#### 6.4.4 未使用

- ファイルごと：TensorCube{Low,High}MixedQuotientAction（これで `{Low,High}MixedCokernelIso(_π_hom)`・`tensorCubeHighMixedCokernel`
  も使われなくなる）、TensorSquareFiltrationImages。
- square 側：`tensorSquareClass_eq_zero_of_acyclic`、`{Positive,Negative}BaseChangeIso_hom_inclusion`、`tensorSquareDecompositionIso`、
  `tensorSquare{Positive,Negative}_inclusion_swap`、`tensorSquareEvaluation_concrete`、`tensorSquareClass_shift_one`・`_cone`、
  `tensorSquareKernelFirstMap_mono`、`tensorSquare{Positive,Negative}Map_homotopyEquivalence`、`tensorSquareKernelFirstMap_mixedLeft`・
  `Right`（`@[simp]`）、`tensorSquareMixedPositiveNegativeIso`、`tensorSquareMixedCokernelIso(_π_hom)`、
  `tensorSquareDiagonal{Involution,_perfect,_support}`、`tensorSquare{Positive,Negative}FourIso`。
- cube 側：`tensorCubeDecompositionIso`、`tensorCubeEigenspace_support`・`_inclusion_rotation`、`tensorCubeEigenspaceMap_id`・`_comp`・
  `_homotopyEquivalence`（これで `tensorCubeEigenspaceMap`・`_quasiIso`・`tensorCubeProjector_naturality`・`tensorCubeEigenspace(_perfect)`
  も不要。cube の類は `tensorCubeAction` の `weightedK0Class` だけで済んでいる）、`tensorCubeClass_eq_zero_of_acyclic`、
  `tensorCubeEvaluation_concrete`・`shift_one`・`cone`、`tensorCubeKernelFirstMap_mono`・`_rotation`、`FirstLayerToKernel_mono`
  （instance）、`FirstLayerFirstMap_mono`・`_toKernel`、`tensorCubeLowMixedMap_epi`、`tensorCubeHighMixedSection{0,1,2}X_inclusion`。
- 再利用の価値：square の固有分解 API（Koszul 側で使う可能性）、`*_shift_one`・`*_cone`（論文の記述に対応、一般の評価構成の補題として）、
  `tensorSquareKernelInclusion_range`。
- 削除に伴い利用者がいなくなる：PerfectComplex/CubicActionTransport、CategoryTheory/CubicConjugation、CategoryTheory/ShortExactCokernel。

#### 6.4.5 提出候補

- HomologicalComplex の Koszul 符号付き symmetric monoidal 構造（§4.3.5 と同じ）。
- 前加法的・R 線形・冪等完備な圏で τⁿ = 1、n 可逆、1 の原始 n 乗根があるときの指標の射影子分解（`Action C (Multiplicative (ZMod n))` の上に）。
- 小物：HomologicalComplex の biproduct の各次数の hom_ext、「q が epi で各次数が射影的なら q ⊗ q も epi」。

#### 6.4.6 リスク

- `*_cup` を C・H に入れると循環。それ以外の縮約では閉路はない。
- F・G・H は重い（Additivity は 1.2M heartbeats）。統合すると再ビルドがまとめて重くなる。
- `set_option backward.defeqAttrib.useBackward true` は cube 側だけ。ファイルの先頭に一律で置くと square 側の挙動が変わりうるので
  section 単位で保つ。

### 6.5 二乗と三乗の一般化（KT2・KT3・PerfectComplex の PC2・PC3 で共通）

調査の四つの報告が独立に同じ構造を指摘した。

- (a) 作用の型が 2 本ある：`CochainInvolution`（τ² = 1、射影子 (1±τ)/2、類 [P₊] − [P₋]）と `CochainCubicAction`（τ³ = 1、
  射影子 (1/3)Σ a^{−k}τ^k、類 Σ ζ^j ⊗ [P_j]）。前者は後者の p = 2、t = −1、ζ = −1 の場合。一般形は `CochainCyclicAction n`
  （τⁿ = 1、n 可逆、1 の原始 n 乗根 t）、射影子 e_j = (1/n)Σ t^{−jk}τ^k（§6.3.3 の Lagrange 補題を End(K) に適用）、
  類 `weightedK0Class E ζ = Σ ζ^j ⊗ [im e_j]`。注意：`tensorSquareClass` は K0WithSupport に値を持ち、Coefficients ℤ（ℤ ⊗ K0）とは
  定義上等しくないので、square 側の利用者 6 ファイルのために `ℤ ⊗ K0 ≃ K0` で包む定義を残す。
- (b) 二乗と三乗の層が 1 対 1 に並行（本体、naturality、perfect・support、擬同型、底変換と固有空間、テンソル、Additivity・Evaluation・
  Multiplicativity、cyclic の 6 対）。一般形は `tensorPow n P` と巡回生成元 `rotation n P`。ただし rotation^n = 1 と shuffle との可換性は
  n ごとの符号計算が要り、一般の n では重い。n ∈ {2,3} に限り「rotation、rotation^n = 1、naturality、テンソル同変性」の 4 つの入力から
  残りを出す構造体（例 `CyclicTensorPowerData n`）を作るのが現実的。PerfectComplex 側で「X ↦ X^{⊗n} は対称モノイダル関手で μ は Sₙ 同変」
  という一般論を一度書けば、符号計算もその具体化になる。
- (c) 核・余核への作用の制限が 5 回手で書かれている → `kernel.map`・`cokernel.map` と「同変な写像の核に作用が降りる」補題一本。
- (d) 混合成分の打ち消し（square の A⊗D ⊞ D⊗A、cube の cyclic sum）は「誘導表現では全固有空間が同型なので Σ ζ^j = 0 から類が 0」と
  いう同じ事実。`cochainCyclicSum n (X_0..X_{n−1})` と `weightedK0Class = 0` を一度だけ示す。PerfectComplex の TensorTripleCyclicSum も
  同じ。
- (e) Koszul の明示モデル（約 3800 行）は K(a)^{⊗n} ≅ K(a) ⊗ Λ^•(H)（H は和が 0 の超平面、n 可逆）の n = 2、3 の場合。
  一般形は「基底変換 K(f) ≅ K(f∘g)」と「K(f₁ ⊕ f₂) ≅ K(f₁) ⊗ K(f₂)」を一般に示し、Fourier 行列で H を対角化する 2 段。
  素数 p では weightedK0Class が p[K(a)] になる（Atiyah の巡回冪の計算）。これで 25 ファイル超が一系統になる。
- (f) フィルトレーション全体の一般の n は部分集合の添字と符号で重く、論文に要るのは n = 2、3 だけなので記録だけにとどめる。

費用対効果の見立て：(a)〜(e) の全面一般化は KT2・KT3・PerfectComplex の Involution*・CubicAction*・TensorTriple* をすべて巻き込む大工事。
短期にはすぐ効くものから行う：§6.3.3 の Positive・Negative の ε による一本化と Shift k の一般化、Lagrange 射影子の共通化、Fourier 座標の
行列化、§6.4.2 の `kernel.map`、§6.4.3 の成分の `Fin 3` 化、§6.3.4・§6.4.4 の削除（KT2 で約 1500 行、KT3 で 1000 行超の削減見込み）。
全面一般化（(a)・(d)・(e)）は PerfectComplex の PC3 の結果と合わせて判断する。

### 6.6 順序の案

PerfectComplex との層の境界は §4.5.1 で合わせて決める
（PerfectComplex を下の層にし、`PerfectModuleResolution`・`K0WithSupport.mk_shift` を PerfectComplex へ、PerfectComplex の IntegerEuler 系・
Adams の Koszul・FiniteProjectiveResolutions を KTheory へ）。KTheory 単体の順序：

1. 削除だけで済むもの：KT1 の再エクスポート 2 本（dévissage は残して軽くする、G の 5）、KT2 の互換 7 本と未使用ファイル 3 本、
   KT3 の未使用ファイル 3 本と §6.3.4・§6.4.4 の未使用。BS/CLMST の再ビルドは起きない。
2. Mathlib への置き換え：KT1 の `baseChange`・`liftBaseChange`・`exact_subtype_mkQ` など、KT2 の `aeval_apply_of_mem_apply_eq_smul`・
   `commute_pow_left_of_commute`・`cubicCoefficientRoot` の def 化、KT3 の `kernel.map`。
3. 群内の一本化：KT1 の局所化完全列と Euler 加法性、KT2 の Positive・Negative の ε 化と Shift k と Fourier 座標の行列化と cyclic 2・3 の
   naturality の共通補題、KT3 の Evaluation の一般構成と成分の `Fin 3` 化。
4. ファイルの統合（KT1 → 12 本、KT2 → 10 本、KT3 → 8 本）。KT2・KT3 の境界の import は同時に縮約して閉路を確かめる。
5. §6.5 の位数 n の作用・n 重テンソル・Koszul の一般化（PerfectComplex の PC3 §6.4.5 と同時）。最も大きい工事なので、1〜4 の後に費用対効果を
   見て判断する。

## 第7章 Asymptotic

### 7.1 中身と外への影響

論文 §7.4–5 の漸近的な「階数の商」の道具。

- `FreeSequence R s`（階数が O(s) の自由加群の列）、その有界ホモトピー圏 `SequenceHomotopy`、小さい階数の対象による Verdier 商
  `SequenceRankQuotient`、スカラーの台を持つ部分圏、冪等完備化、環の取り替え。
- 超極限で正規化した長さ・Betti 数・Euler 標数（`normalizedLimit`）、Koszul の公式、極小分解からの下からの評価。
- もう一本の流れ：長さが有界な加群の列、その Serre 商・導来商、t 構造、一様な持ち上げ。

- **BhattScholze・CLMST は Asymptotic を import せず、名前も使わない。** 改名・移動の波及は Paper/Section4・5 と監査だけ。
- 層は綺麗：Asymptotic は Paper・BS・CLMST を import しない。
- 逆向きの import が 1 か所：`DifferentialGraded/Verdier/OrderSquare.lean` が `Asymptotic.PaperRankQuotient` を import する。その先
  （ChecksOrderSquare・U17 → ChecksU17Integration）はどこからも import されずビルドされない。DifferentialGraded の計画で扱う。

### 7.2 統合（87 → 約 12 ファイル）

| 新しいファイル | 元のファイル |
| --- | --- |
| NormalizedLimit（軽い：Mathlib の解析だけ） | NormalizedLimit・NormalizedLowerBound、EulerLimit の `normalizedLimit_finsum`、LengthFamilies の最初の 3 補題 |
| FreeSequence | FreeSequence・SequenceLinear・FreeSequenceBaseChange、RankQuotient の `FreeSequence.*` |
| SequenceComplex | SequenceComplex・AssembleComplex・SequenceDerived・SequenceResolution・FreeSequenceTensor |
| RankQuotient | RankQuotient・RankQuotientBaseChange・SupportedRankQuotient・SequenceSupport・SequenceBaseChangeSupport・SupportedRankBaseChange・BaseChangeIdentity・BaseChangeComposition |
| SequenceKoszul | SequenceKoszul・SequenceKoszulSupport・SequenceKoszulBounds・KoszulTower・KoszulHomologyLimit |
| SequenceHomology | SequenceHomology・SequenceHomologyBounds・SequenceHomologyLocalization・RankHomologyShift・RankHomologyShiftNatural・CompletedHomology・CompletedHomologyLength |
| Completed | SupportedKaroubi・SupportedKaroubiTriangulated・CompletedRankEvaluation・CompletedKoszulFormula・CompletedComplexEvaluation・CompletedBaseChangeSupport |
| Euler | RankEuler・RankEulerAdditivity・RankEulerComparison・CompletedEulerAdditivity・CompletedEulerComparison・CompletedK0Comparison・EulerLimit の残り |
| Minimal | MinimalResolutionFamily・MinimalSupport・MinimalTruncationComparison・MinimalBettiEvaluation・RankMinimalLowerBound・RankVanishing |
| PaperQuotient | PaperRankQuotient・PaperRankEvaluation・PaperSupportChange・FactorizationSupport・TruncationComparison・ComplexEvaluationIndependence・PaperBaseChange・BaseChangeComparison・PaperBaseChangeEvaluation・PaperComplexBaseChange・PaperTwist・PaperTwistLowerBound・LocalBaseChangeBounds・OrdinaryTwistEvaluation・PaperMinimalLowerBound |
| LengthSequence | ModuleSequence・LengthBoundedSequence・LengthSerreQuotient・LengthQuotientValue・SmallLengthSerreQuotient・FamilyHomologyTruncation・FamilyPostnikov |
| UniformLift | SupportedDerivedImage・SupportedPureDerivedImage・SupportedUniformLift・SmallSupportedUniformLift・RankSmallHomologyCriterion・SmallRankHomologicalKernel・SupportedSequenceTStructure・SupportedRankTStructure・OrdinaryHeartResolution |

- 外へ回す：KoszulBaseChange（30 行、Koszul だけを import）→ CommutativeAlgebra/Koszul。EulerLimit の `lengthHomology_zero_outside`・
  `lambdaEuler_isBigO` → Asymptotic/NormalizedLimit（D の 9：AsymptoticLengthBounds 自体も Asymptotic へ移る）。FamilyPostnikov・FamilyHomologyTruncation（導来圏の ℕ 族）
  → HomologicalAlgebra。`uniformlyPowTorsion` と Serre 類のインスタンス（ModuleSequence）は CommutativeAlgebra/PowTorsionCategory と同じ型の
  議論なので、そちらから点ごとに導く。
- PaperQuotient の 15 本は論文 (4.2)・ひねり・K₀ の作用など論文固有の主張。Paper/Section4 へ移す（G の 3 で決定。Paper が import し、Paper を
  import しないので安全）。

### 7.3 死んだファイル

- FreeSequenceGenerator・LengthDerivedQuotient・SmallLengthDerivedQuotient・PaperRankGenerators・PaperVanishing。到達できるのは
  `Paper/Section4/Foundations`（26 本の import と docstring だけの再エクスポート。importer はルートだけ）経由と、それ経由でしか届かない
  FlatRealization 経由だけ。Foundations と一緒に削除する。
- CompletedK0Comparison は唯一の定理が未使用で、PaperBaseChange への import の中継だけ。統合で消える。

### 7.4 Mathlib との重なり

- `isBigO_of_nonneg_le` → `Asymptotics.isBigO_of_le`（＋`Real.norm_of_nonneg`）か `IsBigO.of_bound 1`（確度高）。
- `moduleSequence_shortExact_eval` は `ShortExact.map`（確度高、インライン化）。
- `normalizedLimit` の `_add`・`_const_mul`・`_sum`・`_nonneg`・`_mono` は `Tendsto.limUnder_eq` の薄い包み。有界性の段は
  `isBigO_iff_isBoundedUnder_le_div` と `IsCompact.ultrafilter_le_nhds` で短くできる（確度中）。
- `FreeSequence.changeMatrix` は `Matrix.map` の見込み（確度中、未確認）。

### 7.5 一本化

- **商の二本立て**：「Completed」（Verdier 商 → Karoubi）と「Paper」（Karoubi → Verdier 商）が同じ結果を二度示している。
  `completedRankBetti_koszul_formula`・`paperRankBetti_koszul_formula`・`paperBaseChangeBetti_koszul_formula`、`*EulerK0_changeRing` の 3 本、
  `*ChangeRingIdIso`・`*ChangeRingCompIso` は 5〜6 の水準で作られ、不変量の族（supportedRank*・completedSupported*・completedRank*・paperRank*・
  paperBaseChange*）ごとに `_nonneg`・`_iso`・`_hasFiniteSupport`・`_triangle`・`EulerK0_mk` が繰り返される。
  → CategoryTheory の `homologicalEulerK0` の形の一般 API（ホモロジー的関手 → Betti・Euler・K₀）に寄せ、各水準はその例にする。
  `maxHeartbeats 800000` の 19 か所（13 ファイル）はすべて Paper 側で、一本化で減らせる見込み。
- Small 版と通常版：LengthDerivedQuotient と SmallLengthDerivedQuotient は Serre 類と引数（U・hU・hs）以外行単位で同じ。LengthSerreQuotient と
  SmallLengthSerreQuotient、SupportedUniformLift と SmallSupportedUniformLift も並行。Serre 類（`IsSerreClass` の述語）を引数にして一度だけ書く。
- `RankHomologyShift` の点ごとの同型を `RankHomologyShiftNatural` で自然同型として作り直している。自然同型だけを残す。
- `normalizedLimit_finsum` は `normalizedLimit_sum` の包み。
- PerfectComplex との並行（形が似ているだけ、確度中）：`minimal_rank_isBigO/_isLittleO` と `resolutionFamily_rank_isBigO/_isLittleO`、
  `isBigO_of_nonneg_le` と `ennreal_isBigO_of_le_sum_nsmul`。

### 7.6 未使用（全 87 ファイルを名前で走査。instance 約 40 は暗黙に使われるので除く）

`completedSupportedEuler_triangle`、`completedSupportedEulerK0_toKaroubi`、`completedSupportedBetti_nonneg/_iso`、
`completedSupportedEulerK0_changeRing`、`completedRankEuler_triangle`、`familyHomology_truncLE/_truncGE_lengthBounded`、
`changeRing_rank`（simp）・`changeRing_rank_isLittleO`、`lengthFamily_isLittleO_iff`、`lengthFamily_normalizedLimit_zero_iff`、
`lengthQuotientValue_obj`（simp）、`sequenceLength_le_of_mono/_of_epi`、`minimal_truncated_paper_supported`、`normalizedLimit_generator_pos`、
`sequenceResolutionHomologyZeroIso`・`sequenceResolutionHomology_isZero`、`paperBaseChangeBetti_nonneg`、`paperSupportedRank_eq_of_radical_eq`、
`completedSupportedEuler_image`、`supportedRankEuler_triangle`、`supportedRankEulerK0_changeRing`、`completedRankEuler_pos_of_minimal`、
`exists_model`、`sequenceRankQuotient_smallComplex_isZero`、`SequenceKaroubi`、`sequenceKoszulHomology_normalizedLimit_eq_zero`、
`supportedKaroubi_essImage`、`supportedDerivedImage_pure`、`supportedRankQuotient_retract`、`supportedRankTStructure_bounded`、
`supportedRankKaroubi_has_representative`、`supportedSequenceTStructure_evaluation_tExact`、`supportedDerivedImage_finiteAmplitude`、
`paperTruncation_K0_eq`、`exists_uniform_nat_bound`（提出しないなら）。死んだファイルの中のものは §7.3 で消える。
`completedSupportedEuler_hasFiniteSupport`・`completedSupportedBetti_hasFiniteSupport` は `scripts/audit_euler_betti_finite_support.lean` が使うので残す。

### 7.7 その他

- `hs : ∀ n, 0 < s n` がほぼ全補題に通されている。構造体（正の列）か型クラスにまとめる。LengthDerivedQuotient・LengthSerreQuotient は
  証明の引数（U・hU・hs）を圏・型の引数に持っていて扱いにくい。
- 一般的すぎる名前（`SerrePositivity.Asymptotic` 直下）：`isBigO_of_nonneg_le`、`exists_uniform_nat_bound`、`exists_model`、
  `map_coordinate_mem_ideal`、`below_rankSmall`、`paper_inclusion_isIso`、`scalar_zero_of_factorization`。
- `paper*`・`Paper*` の接頭辞は出典を表していて数学の内容を表していない。Paper/Section4 へ移すなら名前を見直す。
- `completedSupportedChangeRing` の `@[implicit_reducible]` が要るか確かめる。

#### 提出候補

関手圏での完全性が評価で判定できること（`moduleSequence_exact_of_eval` の一般化）、`nonneg_add_isBigO_iff`・`nonneg_add_isLittleO_iff`、
O(s) の列の f/s は超フィルターに沿って収束する（`normalizedLimit_tendsto`）、ENNReal の `toReal` と `limUnder` の交換。

### 7.8 章の中の作業順

1. 死んだファイル 5 本と Paper/Section4/Foundations、未使用の削除（BS/CLMST の波及なし）。
2. 確度高の Mathlib への置き換え、KoszulBaseChange などの外への移動。
3. 統合（§7.2）。
4. 二本立ての一本化（§7.5、大きい）。Small 版の一本化。

決定済み（G の 3）：PaperQuotient（15 本）は Paper/Section4 へ移す。二本立ては Paper 側を正にし、Completed 側の結果は比較の同型で導く（段階 3）。

## 第8章 CLMST

### 8.1 分類の結果

| | ファイル | 行 |
| --- | --- | --- |
| A（基礎） | 58（Prop247 20、その他 38） | 約 4200 |
| M（混在、A の部分を下ろし B を残す） | 19（Prop247 7、その他 12） | 約 2300 |
| B（論文） | 69（Prop247 30、その他 39） | 約 5700 |

- A のうち **BS より下へ下ろせる**もの：約 35 本・2000 行以上（§8.2.1）。
- A のうち **BS に依存する**もの：約 30 本（§8.2.2）。BhattScholze/ の下へ。
- CLMST の外で使われる名前：`proposition_2_4_7_proved`（CLMST/Inputs/PerfectoidIsogeny が包む）、Paper/Section2/MixedPerfectoid が再エクスポート
  する `Section2.MixedPerfectoid` 一式、BS/Almost/PerfectoidAlmost が使う `CLMST.perfectoidIdealMod`、`Inputs/CLMST.lean` 経由の主定理。
- `scripts/audit_clmst.lean`（1428 行、`CLMST.` の参照 195）・`audit_clmst_b3.lean`・`scripts/audit/clmst.lean` が古い名前とパスを固定している。
  移動・改名のたびに直す（許可済みの範囲）。

### 8.2 基礎（A）の行き先

#### 8.2.1 BS より下へ（CommutativeAlgebra・HomologicalAlgebra・LengthAlgebra）

| 行き先 | 元（CLMST/ からの相対） | 注意 |
| --- | --- | --- |
| CA/EtaleRankStratification（新設） | Prop247RankLoci・RankTransport・RankPrincipal・RankProduct・RankProductAway・RankBaseChange、Prop247RankImages の `rankOpen*` | Mathlib：`awayRank_isLocallyConstant` = `Module.isLocallyConstant_rankAtStalk`（確度高）、`awaySpectrumHomeomorph` は `localization_away_isOpenEmbedding`＋`localization_away_comap_range`（確度高）、階数の基底変換は `Module.rankAtStalk_baseChange`（確度中〜高）、`rankOpen_exists_basicOpen` は `existsUnique_idempotent_basicOpen_eq_of_isClopen`（確度中） |
| CA/ReducedFiniteFreeIsogeny 付近 | Prop247RankCone（R → ∏ R_n の錐が g の冪で消える） | HA/TwoTermConeAnnihilator を使う |
| CA/IntegralAwayExtension | Prop247RankValuation（死んでいる、§8.4）・Prop247FiniteComparisonValuation（付値環への一意な拡張） | |
| CA/ReducedSectionImage 付近 | Prop247RankImages の `openSectionImage*`・`toOpenSectionImage*` | `zeroLocus_vanishingIdeal_eq_closure`（部分的） |
| CA/FinitePresentationIsogenyLift | Prop247FiniteFreeComparison、Prop247CommonSquare（局所化した分解） | FiniteFreeConeIsogeny を先に下ろす |
| CA/RootTower/BaseChange（新設） | StageAlgebra の `StageAlgebra`・instance・`stage0*`、StageBaseChange・StageDimension・StageFiniteness・StageLocality・StageResidueLength・StageParameterChange・CompletedStageBaseChange・StagePowerMembership、StageTensor の `stageToCompletedTower`・`stageToCompletedTensor` | BS への依存は StageAlgebra → CLMST.Algebra 経由だけ。StageAlgebra を分ければ外れる。`stageAlgebraIsNoetherianOfBase` は優先度 90 の大域 instance |
| CA/RootTower/ModP* の隣 | StageModPImageLength・StageModPLengthBound | |
| CA/RootTower/Roots 付近 | PerfectoidIdealRoots の `completedTowerRoot*`、PerfectoidFrobeniusComparison の塔の部分 | |
| CA/GenericEtale | EtaleLocus（`exists_finite_etale_away_of_charZero` の 1 行の包み、インライン化） | |
| CA/RegularLocalRing・FrobeniusHypersurfaceGrowth | ModPHypersurfaceGrowth、RPerfdCohomologyInputs の `parameter_power_isKoszulResolution` | |
| CA（局所化の共通模型、E 群） | PerfectoidEtaleCommonCover・PerfectoidFinitePresentationCommonModel | |
| CA/PrincipalMaximalFactorization | CyclicFactorReduction の `exists_p_power_factor_of_nonzero`・`exists_p_power_unit_of_fin_one`（包み） | |
| CA/AlgebraMapCokernel | PerfectoidCokernel の `PerfectoidizationCokernel`・`…RestrictEquiv`・`*_shortExact` | 零化の補題は B（Prop 2.4.7 を使う） |
| HA/TwoTermConeAnnihilator | FiniteFreeConeIsogeny（Claim 2.4.8 の一般形） | |
| HA/CompleteFaithfullyFlatDescent | IsogenyDescent（完全忠実平坦な拡大に沿った錐のスカラーの降下）、`moduleMapConeBoundedAbove` は HA/DerivedModuleCone へ | ConeComparison を動かす前提 |
| HA/DerivedCompletion | Prop247RankCompleteness（→ ModuleClosure）・Prop247ConeComparison（→ CompletedBaseChangeTriangle）・Prop247SourceComparison（→ CompletedFlatBoundedComparison）、Prop247Cone の `prop247_source_isModuleComplete`・`cone_isComplete_of_perfectoid_target`（→ FinitePresentationComplete）、Prop247Uniform の `prop247_uniform_reductions_of_fixed_cone`、ModuleCompletion（死んでいる） | |
| LA/Almost* | AlmostLength（`length_eq_of_(full_)almost_iso_baseChange` の特殊化、インライン化）、NormalizedAlmostLength の一般部分 | |
| LA/RootTowerLength/CompletedQuotientEvaluation | RootFiltrationBound の `completedLength_quotient_le_root_factor*` ほか 3 つ | |

- Mathlib への置き換え：`iterate_pow_apply` = `congrFun (pow_iterate p m) x`、`pow_sub_mem_of_sub_mem` は `sub_dvd_pow_sub_pow` から（ともに確度高）。

#### 8.2.2 BhattScholze/ の下へ（BS に依存するもの）

| 行き先 | 元 |
| --- | --- |
| BS/Almost/PerfectoidAlmost | BasicSetup、Inputs/BasicSetup（`perfectoidIdealMod_idempotent`、重複、§8.3）、Almost（`perfectoidIdealMod` ほか。§8.5 の逆転を解消） |
| BS/Almost（新 PerfectoidIdealTor） | PerfectoidIdealCompletedMul、PerfectoidIdealTorCover・TorRoots・TorTransport・TorComparison・ExcisionTor、KLAicTorFromExcision の A 部分 |
| BS/Andre | AndreTorDescent・AndrePerfectoidizationTorDescent・AndrePerfectoidIdealTorDescent、Prop247AndreBase（→ AndreFlatness） |
| BS/Perfectoidization（Excision など） | PerfectoidizationExcisionComparison・PerfectoidizationImageTorComparison・PerfectoidFiniteProductTor・CanonicalExcisionTorInput・KLFiniteComparisonExcision（BS Cor 8.12 による excision。今は B の KLCohomologyFromExcision を import しているので先にほどく）・KLOriginalTorFromExcision・KLCanonicalSingleTriangleBridge の A 部分、PerfectoidizationCone、TensorOrder の `IsPerfectoidization.comp_ringEquiv` |
| BS/Semiperfectoid | Prop247IdempotentQuotient（完全環を冪等元で割っても perfectoid）・Prop247QuotientPerfectoidization（→ Surjectivity）・Prop247ProductComponents・Prop247ProductUniversality・Prop247ProductPerfectoid（死んでいる）・Prop247RankProductUniversality の A 部分 |
| BS/Perfectoidization/CompletedTensor・CompletedBaseChange | Prop247TensorUnit・Prop247TargetComparison（`prop247_targetTensorAlgEquiv` は `.choose` でデータを作っている。持ち上げの def に） |
| BS（perfectoid イデアルの根） | PerfectoidIdealRoots の `perfectoidQuotient`・`perfectoidIdealQuotientEquiv`・`mem_perfectoidIdeal_of_pow_mem_span*` など、PerfectoidFrobeniusComparison の一般部分（`quotientRootFrobenius*`・`root_mem_sup_*` など）、CyclicFactorReduction の `perfectoidIdeal_le_of_p_power_factor` |
| HA/DerivedCompletion/PowerTorsionTorExtension | AllModuleAlmostTor（`tor_eq_zero_of_power_torsion_and_complete_extensions` の 1 行の包み、死んでいる） |
| 共有の対象（Paper と CLMST） | Algebra の `Section2.MixedPerfectoid`・`toMixedPerfectoid`・`isPerfectoidization_toMixedPerfectoid` と instance → BS 側の根の塔の perfectoid 化（例 `BhattScholze/…/RootTowerPerfectoidization`）。`CLMST.RPerfd`（その別名）は B に残す |

- BS に依存する A を CA に置かない方針なので、CA にすでにある BS への依存（PerfectoidIdeal 系・AbsolutelyIntegrallyClosedPerfectoidQuotient・
  MonicRelationRegularSequence など、§2.8.1）も同じ作業時間に BS 側へ移す。
- `prop247_` の接頭辞は一般の事実にも付いている（`prop247_isIntegralPerfectoid_idempotent_quotient`・`prop247_completion_unit_surjective`・
  `prop247_awaySpectrumHomeomorph` など）。下ろすときに数学の内容の名前へ改名する。

### 8.2.3 Prop 2.4.7・Claim 2.4.8・Prop 2.4.9 まわりの補足（2026-10-30 の確認）

- 前提（`#print axioms`・`#print sorries` で確認済み）：`CLMST.Inputs.proposition_2_4_7`（2.4.7）と `CLMST.perfectoidIdeal_powerTorsionTorInput`
  （2.4.9(a)、主イデアル版）の sorry の出どころは `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3` だけ。`CLMST.finiteFreeConeIsogeny`
  （Claim 2.4.8）の公理は標準の 3 つだけ。import の閉包では 2.4.9(a) は 2.4.7 から独立（Corollary404 の閉包に Prop247* は入らない）。共有するのは
  述語 `KLFiniteComparisonExcision` と PerfectoidEtaleCommonCover。2.4.9(b)（almost 忠実性）とその系、Thm 4.0.3(b) は形式化しておらず、主経路で
  使わないので対応不要。
- **Prop 2.4.9(a) の主張の置き場所**：`perfectoidIdeal_powerTorsionTorInput` は CLMST/KLFiniteComparisonExcision.lean:76 にあり、§8.2.2 の表は
  このファイル全体を BS/Perfectoidization へ送っている。ファイルを分ける：excision の証明 `klFiniteComparisonExcision_of_perfectoid` は BS へ、
  主張 `perfectoidIdeal_powerTorsionTorInput` は論文側（§8.3 の Thm403a か 2.4.9(a) 専用のファイル）へ。主張の側は論文側の KLCohomologyFromExcision
  ほかを使うので、BS へ移すと層が逆転する。区切り 2a の手順に入れる。
- **同じ述語の証明が 2 つ**：`prop247_finiteComparison_excision`（CLMST/Prop247Proof.lean:42）と `klFiniteComparisonExcision_of_perfectoid`
  （CLMST/KLFiniteComparisonExcision.lean:39）は、どちらも `KLFiniteComparisonExcision R p` を、BS Cor 8.12 の excision に導来完備性と主局所化の
  条件を与える形で証明している。今は後者のファイルが論文側の KLCohomologyFromExcision を import しているので Prop247Proof から使えない。上の分割で
  後者を BS へ移せば import できるので、一本化する（区切り 2a）。
- **古い docstring**（§8.3 の統合のときに直す）：`KLFiniteComparisonExcision` の定義（CLMST/KLAicTorFromExcision.lean:39）の「Unproved excision input …
  the pullback assertion has not」、Prop247 系（ConstantRankExcision・ExcisionLocal・CanonicalRankDescent・RankData・RankComponentExcision など）と
  KLAicTorFromExcision・KLOriginalTorFromExcision・CanonicalExcisionTorInput・KLCohomologyFromExcision の「条件付き」「未供給入力」「明示入力のまま」、
  CLMST/Inputs/PerfectoidIsogeny の「元の文献入力と同じ署名」、Inputs/CLMST の「文献入力は CLMST/Inputs/」。いずれも今は証明済みのものを指している。
  2.4.7 の証明が Rem 2.4.6（Σ_r Galois 閉包）の代わりに Zariski 局所的な分解と Cor 8.12 を使っていることは、統合後のファイルの docstring に残す
  （解説の段落 par:bs-cor812 と同じ内容）。
- **Claim 2.4.8 の扱い**：§8.2.1 は FiniteFreeConeIsogeny を HA/TwoTermConeAnnihilator に下ろすので、論文の番号は docstring にしか残らない。
  有限代数版 `finiteAlgebraConeIsogeny` は使い手がない。論文側に薄い入口を残し、`finiteAlgebraConeIsogeny` は削除する（G の 9 で決定）。

### 8.3 論文（B）の構成

Prop 2.4.7 の証明の骨組み（実際に使われている経路）：
`proposition_2_4_7_proved` → `prop247_isogeny_of_specified`（Proof：BS Cor 8.12 の excision に完備性 RankClosedSides と付値の拡張
RankSourceValuation・FiniteComparisonValuation を与える）← 一般階数の降下 `prop247_exists_canonical_generalRank_descent_data`
（CanonicalRankDescent ← GeneralRank・AndreBase・RankData・RankProductUniversality・CoveredDescent）← RankData ← RankComponentExcision
（各階数の成分に定数階数の結果を適用。RankAIC・AicRankAssembly ← AicRankCoefficients ← AicRankImages・RankBaseChangeDiagram・RankCone）。
定数階数：ConstantRankExcision ← ExcisionLocal ← LocalComparison（CommonSquare＋Uniform）。降下の背骨：CoveredDescent ← UniformStandard ←
StandardCone ← StandardSquare（SourceComparison・TargetComparison・TensorUnit・ConeComparison・Uniform）← IsogenyDescent（D1–D6）。

| 新しいファイル | 元 |
| --- | --- |
| Prop247/Descent/Uniform | Uniform（B 部分）・CoveredDescent・UniformStandard |
| Prop247/Descent/StandardSquare | StandardSquare・StandardCone（A 部分は §8.2 へ） |
| Prop247/ConstantRank | LocalComparison・ExcisionLocal・ConstantRankExcision |
| Prop247/Rank/Targets | RankTargets・RankAIC |
| Prop247/Rank/Diagram | RankBaseChangeDiagram・RankAssembly |
| Prop247/Rank/AIC | AicRankImages・AicRankCoefficients・AicRankAssembly |
| Prop247/Rank/ComponentExcision | RankComponentExcision・RankData |
| Prop247/Rank/TargetComparison | RankTargetComparison・RankProductUniversality（B 部分） |
| Prop247/Rank/ClosedSides | RankClosedSides・RankSourceValuation |
| Prop247/GeneralRank | GeneralRank・CanonicalRankDescent |
| Prop247/Proof | Proof |
| Prop247/Consequences | PerfectoidIsogeny・Inputs/PerfectoidIsogeny・TensorIsogeny・CompletedTensorIsogeny・NonunitIsogeny、Algebra・StageAlgebra の RPerfd・`toRPerfd` |
| Thm403a | AllModuleTorFromBS・CompletedTowerAllModuleTor・ConditionalCohomologyFromPowerTorsion・KLAllModule（主経路から外れている、§8.4） |
| Cor404 | ConditionalCohomologyVanishing・FiniteStageKoszulAnnihilator・RPerfdCohomologyInputs（B 部分）・RPerfdTorBaseChange・KLCohomologyFromExcision・Corollary404・CohomologyVanishing・Inputs/CohomologyVanishing |
| Prop4010 | Cyclic*（8 本）・RootFiltrationBound（B 部分）・NormalizedAlmostLength（B 部分）・Inputs/AlmostLength |
| Prop4014 | PerfectoidCokernel（B 部分）・PerfectoidCokernelEuler・CompletedCokernel{Koszul,Length,FiniteEuler}・CompletedSourceLength・SourceEulerEvaluation・CompletedTargetLength・SelectedParameterEuler・CompletedParameterFiniteness |
| Claim4015 | ParameterLastPowerLength・ParameterFormulaDescent・ParameterLength・Inputs/ParameterLength |

- `CLMST/Inputs/` は名前と中身が合っていない（すべて証明済みで引用ではない）。上の表のとおり節のファイルに吸収して Inputs/ をなくす。
- `hetale : letI := GenericEtale.awayAlgebra … Algebra.Etale …` の長い仮定が約 15 の主張で繰り返される。名前付きの述語にする。

### 8.4 死んだもの・主経路から外れているもの

- Prop247 の死んだファイル（10 本・676 行。importer はルートと `scripts/audit/clmst.lean` だけ）：ActualDescent・Conditional・CompletedDescent
  （古い「条件付き」の終点）、ConstantRank・ConstantRankDescent・RankDescent（並行していた定数階数の経路）、AicRankValuation・RankValuation
  （RankSourceValuation・FiniteComparisonValuation の重複）、FiniteFreeCover、ProductPerfectoid。
- その他で `Inputs/CLMST.lean` から届かないもの：Thm 4.0.3(a) の全加群版の一群（AllModuleAlmostTor・AllModuleTorFromBS・CompletedTowerAllModuleTor・
  ConditionalCohomologyFromPowerTorsion・KLAllModule）、CompletedCokernelKoszul、KLCanonicalSingleTriangleBridge、ModuleCompletion、
  PerfectoidIdealExcisionTor・PerfectoidIdealTorComparison・PerfectoidIdealTorRoots、TensorOrder、Inputs/AlmostLength。
  **決定（2026-10-30）**：Thm 4.0.3(a) の一群は論文の内容なので残す。残りは A の部分を下ろしたうえで削除（論文の主張を含むものは残す）。
- `corollary_4_0_4` が `CLMST`（Corollary404）と `CLMST.Inputs`（Inputs/CohomologyVanishing）に 2 回定義されている。一つに。
- mod p^N の冪等性の証明が 2 通り（BS 側の `perfectoidIdealMod_idempotent` と `CLMST.Inputs.perfectoidIdealMod_idempotent`）と、BasicSetup の
  `Fact` の包み。一つに（BS 側の名前は `scripts/audit_bhatt_scholze_b5.lean` だけが使う）。
- 不要な import：Corollary404・CyclicLength・Inputs/CohomologyVanishing・Inputs/ParameterLength の `Mathlib.RingTheory.WittVector.Basic`・
  `MvPowerSeries.Basic`。

### 8.5 層の逆転 2 か所

- **BhattScholze/Almost/PerfectoidAlmost → CLMST.Almost**：`BhattScholze.perfectoidIdealMod_idempotent` の中で `CLMST.perfectoidIdealMod` を
  使うためだけ。Almost.lean を BS/Almost/PerfectoidAlmost の側へ移せば解消（§8.2.2）。
- **Paper/Section2/MixedPerfectoid → CLMST.Algebra**：11 行の再エクスポート。`Section2.MixedPerfectoid` 一式を BS 側の根の塔の perfectoid 化へ
  移せば解消。Paper/Section2/MixedPerfectoid は削除して importer を張り替える。

### 8.6 順序（第二層の作業時間の中で）

1. CLMST の外で使われる名前を固定（§8.1）。監査の参照の一覧を取る。
2. BS より下へ下ろす A（§8.2.1）：BS への依存がないので、CA・HA・LA の対応する群の統合と同時に行える。CLMST の側は import 行と参照の書き換えだけ。
3. BS の下へ置く A（§8.2.2）と、CA に今ある BS 依存のもの（§2.8.1）を一緒に BhattScholze/ へ。§8.5 の逆転を解消。
4. B の統合（§8.3）、死んだファイルの削除（§8.4）、`prop247_` の改名。
5. `scripts/audit_clmst*.lean`・`scripts/audit/clmst.lean`・`bhatt_scholze.lean` を直し、全依存ビルド 1 回でコミット（BS/CLMST の分は独立コミット、
   旧→新の対応表を付ける）。

### 8.7 決定（記録）

1. ~~BhattScholze/ に新しいファイルを置く作業を誰が行うか~~ → コーディネータが第二層の作業時間に行う（BhattScholze/ を編集しない決まりの、この件の例外。2026-10-30）。
2. ~~Thm 4.0.3(a) の全加群版の一群を残すか~~ → 論文の内容なので残す（2026-10-30）。B の Thm403a のファイルにまとめる。
3. ~~B のファイルの名前~~ → 論文の番号ではなく内容の名前を付ける（2026-10-30）。§8.3 の表の名前（Prop247/…・Thm403a・Cor404・Prop4010・Prop4014・Claim4015）は
   仮の呼び名で、作業時に内容の名前（例：Prop247 → `IsogenyOfPerfectoidization/…`、Prop4010 → `CyclicLengthBound` など）へ置き換える。名前の案は作業前に提示する。

## 第9章 Paper に紛れている一般の補題

`SerrePositivity/Paper/` には論文の主張とその直接の証明だけを置き、一般の補題は共有層へ下ろす。調査（2026-10-30、読むだけ）は
Paper/Section2 の 6 本と Paper/Section5 の 6 本（計約 3600 行）。元の候補は旧 `paper-layer-extraction.md` §2 と
`archive/repository-survey-2026-10-28.md` §6・§7。Asymptotic/NormalizedLimit は第 7 章（§7.2・§7.4）で扱う。

### 9.1 外への影響と前提

- Section2 の 6 本は BhattScholze・CLMST に推移的にも依存しない（import は CommutativeAlgebra・LinearAlgebra・HomologicalAlgebra・PerfectComplex・
  LengthAlgebra/RootTowerLength と Paper/Section2 の互換ファイルだけ）。Section5 の Core・PrimeReduction は NormalizationPositivity 経由で BS・CLMST を
  引く（約 1940 モジュール）が、その中の一般の補題は BS に依存しない。ParameterQuotient・ParameterQuotientCM・GaloisNormalization は BS 非依存。
- この 12 本の宣言を BhattScholze・CLMST は使わない。`scripts/audit/shared.lean` が 12 本すべてを import し、`scripts/audit_clmst.lean` が
  TowerApproximation を import して `SerrePositivity.Section2.μT` を `assert_no_sorry` で確かめている（改名するなら監査も直す）。
- 前提：Section2 を動かす前に、`Paper/Section2/TowerLength.lean`（`towerLength`・`towerLengthFun_eq_fgLength`）と `Paper/Section2/TowerDescent.lean`
  （`towerLengthFun_tensor`、64 行）を LengthAlgebra/RootTowerLength へ移す（どちらも RootTowerLength の薄い包み）。Paper/Section2 の TowerStage・Tower は
  CA/RootTower の再エクスポート（互換ファイル）なので、利用者を張り替えて削除する。
- 名前：Section2 の宣言はすべて `namespace SerrePositivity.Section2`（CA/RootTower・RootTowerLength も同じ）。移すときに `RootTower`（完全化の話は
  `Perfection`）へ付け替える（C の規約、§5.3 の名前空間の統一と同時）。Section5 の一般の補題は `Section5` にある。

### 9.2 ファイルごとの行き先

| ファイル | 一般 | 論文 | 行き先 | BS |
| --- | --- | --- | --- | --- |
| Section2/PerfectApproximation（245） | 約 230 | 0 | 新 CA/Perfection/Approximation（CA/PerfectNormality の隣）。`perfectionApproximation_kernel_bound`（約 17 行、`NormalizedLength` を使う）は LA の核か PerfectComplex/QuotientLength | なし |
| Section2/PerfectApproximationLength（504） | 約 480 | 約 20 | LA/RootTowerLength/PerfectApproximation | なし |
| Section2/PerfectTower（290） | 約 285 | 0 | CA/RootTower/Perfect（塔から完全環への標準写像、約 180 行）・CA/RootTower/StageFrobenius（有限段から底への Frobenius、約 110 行） | なし |
| Section2/PerfectConductor（336） | 約 290 | 約 45 | CA/RootTower/PerfectConductor（CA/TraceConductor を使う）。`exists_tower_perfection_conductor`（論文の仮定を与える部分）は Paper に残す | なし |
| Section2/PerfectBaseChange（437） | 約 410 | 約 25 | CA/RootTower/PerfectBaseChange（CA/SeparableBaseChange・RegularLocalRing を使う） | なし |
| Section2/TowerApproximation（1052） | 約 1010 | 約 40 | LA/RootTowerLength/BaseChangeApproximation（PerfectComplex/TensorResolutionLength を使う）。ENNReal の極限の補題 2 つは Asymptotic/NormalizedLimit か ENNReal の補題のファイル | なし（TowerLength・TowerDescent を先に移す） |
| Section5/PrimeReduction（97） | 約 50 | 約 25 | `ideal_eq_bot_of_quotient_dim_eq` は CA（Krull 次元・SupportDimension）、`chi_self_residueField`・`chi_prime_eq_one_of_dim_zero` は IM/Basic | 一般部分はなし |
| Section5/ParameterQuotient（310） | 約 45 | 約 265 | `length_le_tor_zero_mul`（ℓ(M) ≤ β₀(M)・ℓ(B/I)）は HA の Tor か IM/ParameterQuotient | なし |
| Section5/ParameterQuotientCM（82） | 0 | 82 | 残す（§9.5） | なし |
| Section5/Core（93） | 12 | 約 75 | private の `exists_nat_ringKrullDim` は PrimeReduction の `ideal_eq_bot_of_quotient_dim_eq` と同じ議論。一本にして CA へ | 一般部分はなし |
| Section5/CoreLengthPositivity（113） | 0 | 約 110 | 残す | なし |
| Section5/GaloisNormalization（100） | 約 16 | 約 80 | private の `powerSeriesMapEquiv`・`wittMapEquiv` を CA（PowerSeries・Witt）へ | なし |

一般の部分は合計約 2800 行。主な中身：
- **完全化の近似**（PerfectApproximation）：完全化への pⁿ 乗根の写像 `perfectionRootHom`、根の段 `perfectionRootStage`、近似 `perfectionApproximation`
  （論文 Theorem 2.5 の `B_q`）、`perfectClosure_isDomain`・`perfectClosure_isIntegrallyClosed`・`isIntegral_perfection_of_isIntegral`。
- **長さの極限**（PerfectApproximationLength）：`normalized_frobenius_length_tendsto_perfection_quotient`（ℓ(D/H^{[pⁿ]})/p^{nh} → λ∞(D_perf/H)、Hilbert–Kunz 型）
  と 21 の塔の長さの補題（19 はファイルの中だけで使う）。
- **根の塔と完全環**（PerfectTower・PerfectConductor・PerfectBaseChange）：普遍性 `towerToPerfect`、`towerEquivPerfection`（完備正則局所環で剰余体が完全なら
  塔 ≃ 完全化）、共通の分母（conductor）、`perfectBaseChangeEquiv`（Λ ⊗_{A_n} D^{1/pⁿ} ≃ B_n）。
- **基底変換の近似**（TowerApproximation）：S = Λ ⊗_A T の加群を段の加群で近似し、Tor の極限を取る一般の部分（論文 Lemma 5.4 の一般形）。

### 9.3 Mathlib との重なり

- `perfectionRootHom_injective`・`perfectClosure_lift_injective` は `IsPRadical`・`PerfectClosure.isPRadical` と `injective_comp`（FieldTheory/IsPerfectClosure）から
  （確度高）。`prime_eq_maximalIdeal_of_quotient_dim_zero` は `Ring.KrullDimLE.eq_maximalIdeal_of_isPrime` でほぼ足りる（確度高）。
- TowerApproximation の約 150 行（`fwdAux`〜`fwdT_smul`、`baseChangeTowerEquiv`）は `TensorProduct.AlgebraTensorModule.cancelBaseChange`・
  `Algebra.TensorProduct.cancelBaseChange`・結合子で置き換えられる見込み。`flat_TS` はその同型を通した `Module.Flat.baseChange`（確度中）。
- `PerfectTower` の標準写像は `PerfectRing.lift`・`PerfectClosure.lift` の塔版（Mathlib になし、確度中）。`towerEquivPerfection` は Λ の A 上の
  `IsPerfectClosure` のインスタンスとして書ける（確度中）。
- Mathlib にないもの：`IsDomain (PerfectClosure …)`（`instReduced` だけ）、`perfectClosure_isIntegrallyClosed`、`MvPowerSeries`・`WittVector` の `mapEquiv`、
  ENNReal の挟み撃ち（一般形だけ）。提出候補。

### 9.4 名前と未使用

- TowerApproximation の一文字の略称（`TS`・`TSj`・`ιT`・`φB`・`φS`・`Fj`・`JT`・`μT`・`ψU`・`lenB`）は移すときに内容の名前にする（`μT` は audit_clmst が使う）。
- 未使用：`perfectClosure_lift_injective`、`exists_tower_perfection_conductor_roots_of_normal_base`。

### 9.5 Paper の中で主経路から外れているもの（論文の内容なので残す）

- Section5/ParameterQuotientCM の `lemma_5_3_of_cm`（Lemma 5.3 の Cohen–Macaulay 版）は importer がなく未使用。
- Paper/Section4/FlatRealization（Asymptotic/PaperVanishing を使う）は、段階 0 で削除した `Paper/Section4/Foundations`（再エクスポート）からしか
  届かなかった。今はルートが直接 import する。
- どちらも論文の内容なので残す（論文の内容は残すという 2026-10-30 の決定に従う）。主経路に組み込むかは別に判断する。

### 9.6 順序

1. TowerLength・TowerDescent を LA/RootTowerLength へ、互換ファイル TowerStage・Tower を削除（段階 1 の 4、LA の統合と同時）。
2. Section2 の一般部分：CA へ行くもの（PerfectApproximation・PerfectTower・PerfectConductor・PerfectBaseChange）は段階 1 の 2（CA の残り）、
   LA へ行くもの（PerfectApproximationLength・TowerApproximation）は段階 1 の 4。名前空間を `RootTower`・`Perfection` へ。
3. Section5 の一般の補題（PrimeReduction・Core・ParameterQuotient・GaloisNormalization）は行き先の群の作業と同時。
いずれも BS/CLMST に触れない（audit_clmst の `μT` の行だけ直す）。

## 第10章 Paper の再構成

`SerrePositivity/Paper/`（74 本、約 9800 行）には論文の主張とその証明だけを置き、論文の構成に沿って並べる。調査（2026-10-30、読むだけ）。
一般の補題のうち Section2 の 6 本と Section5 の 6 本は第 9 章で扱った。この章はそれ以外と、Paper 全体の構成。

### 10.1 証明の骨組み（主経路）

- `Statement`（Thm 1.1 `main_statement`、Lemma 5.1 の `core_statement`）が剰余標数で分かれる。
  - 標数 0：`Section5/CharacteristicZeroReduction` → IM/EqualCharZeroPositivity（Serre の対角の議論）。
  - 標数 p：`Section5/CompletionReduction` → `ResidueFieldReduction`（Lemma 2.1）→ `ModuleReduction`（dévissage）→ `PrimeReduction` → `Core`
    （Lemma 5.1）→ `GaloisNormalization`（Lemma 2.2）・`NormalizationPositivity`。
- `NormalizationPositivity`（§5.1・§5.5 の組み立て）は `Section2/Theorem2_5`（Thm 2.5）を使う。その下に `LengthAlgebraConstruction` →
  `MixedLengthAlgebra` → `CompletedTower`・`MixedPerfectoid`、`PerfectQuotientLimit`・`PerfectKoszulLimit` → `PerfectKoszulLength` → `TowerKoszulLength`、
  `TowerLengthOn` → `TowerLength`・`TowerDescent`・`TowerStage`、第 9 章の Perfect*、`LengthAlgebraConsequences`（(2.5)・(2.6)）。
- `NormalizationPositivity` → `SelectedParameterPositivity`（(5.4)、`ParameterChoice`）→ `CoreLengthPositivity` が二つに分かれる。
  - 第一の比較：`Section5/Positivity`（§5.5）→ `Lemma5_2`（Lemma 5.2）→ `FirstComparison`・`NormApplication` → `Lemma3_5`（Lemma 3.5）・`Lemma3_5/{Normalized,Ordinary}`。
  - 第二の比較：`TwistedLengthPositivity` → `ParameterLengthPositivity`（`Preparation`、(5.6)）→ `TowerPositivity` → `ParameterQuotient`（Lemma 5.3・5.4）・
    `RegularLengthAlgebraPositivity` → `LengthAlgebraPositivity` → `ApproximationPositivity` → `ApproximationSecondComparison` →
    `SecondComparison` → `Section4/SymmetricComparison` → `PaperK0Comparison`（Prop 4.5）→ `UniformRepresentative`、および `ApproximationEuler`
    （`ApproximationBetti`・`ApproximationHomology`・`SupportedApproximation`・`MinimalApproximation`・`ApproximationLowerBound`・`FirstComparison`）。
  - ほかに主経路：`Section4/LengthAlgebraRealization`、`Section4/LengthHypotheses`（1 補題だけ使う）、`Section4/SupportedDescent`（Lemma 4.6 と Thm 3.1 の
    帰結。Paper の中の唯一の `sorry`）、`Section2/TowerApproximation`。
- 引用：Inputs/Descent（Thm 3.1）は Lemma 3.5 以下で使う。BhattScholze（81 モジュール）・CLMST（123）・InfinityCategories（312）に届くのは
  `MixedLengthAlgebra`・`MixedPerfectoid`（Thm 2.5 の混標数）経由だけで、Section4 と Section5 の他のファイルは BS に依存しない。

### 10.2 主経路から外れているもの（G の 8：古い経路は削除、変種と論文の主張は残す）

| ファイル | 中身 | 状況 |
| --- | --- | --- |
| Section4/Theorem4_7 | Thm 4.7 | `theorem_4_7` は未使用、`theorem_4_7_K0` は scripts だけ。主経路は SymmetricComparison・SecondComparison で同じ内容を導いている |
| Section4/FlatRealization | λ 平坦性からの比較（変種） | 3 宣言とも未使用。段階 0 でルートから直接 import に |
| Section5/ParameterQuotientCM | Lemma 5.3 の Cohen–Macaulay 版 | 未使用 |
| Section5/AsymptoticPositivity・SecondComparisonLowerBound | 古い正値性の経路（Asymptotic/PaperMinimalLowerBound 経由） | Approximation* の経路に置き換えられている。別証明として残すか、消すか |
| Lemma3_4 | Lemma 3.4 | `lemma_3_4` 未使用。Cor 2.6(1,2) の `cor_2_6_tor` と同じ議論 |
| Section2/Lemma2_4 | Lemma 2.4 | 4 宣言とも未使用 |
| Corollary2_6・Section2/Corollary2_6 | Cor 2.6 | 主経路は重複の `Section4.residue_length_pos_of_lengthAlgebra_values` を使う（§10.4） |

死んでいる（importer はルートと scripts だけ）：上の表の Corollary2_6・Lemma3_4・Section2/Lemma2_4・Section4/FlatRealization・Section4/Theorem4_7・
Section5/AsymptoticPositivity・ParameterQuotientCM と、Section2/MonomialBasis・Section2/Tower（再エクスポート、§10.3）。Section2/Corollary2_6 と
Section5/SecondComparisonLowerBound は、死んでいるファイルだけが import する。

### 10.3 再エクスポートと薄い包み

- 再エクスポートだけ：Section2/Tower・MonomialBasis・TowerStage（CA/RootTower の再エクスポート。区切り 0 の追加分として削除、TowerStage の利用者
  PerfectTower は CA/RootTower/Stage を直接）、Section2/MixedPerfectoid（CLMST.Algebra の再エクスポート。importer は Inputs/CLMST だけ。§8.5 で
  MixedPerfectoid 一式を BS 側へ移すときに削除）。
- 薄い包み：Section2/TowerLength（103 行、`NormalizedLength` を `towerLength` として再エクスポート＋C1・C2）・TowerDescent（64 行）・TowerLengthOn（54 行、
  `towerLengthOn_len` は未使用）・CompletedTower（46 行。Inputs/CLMST が import している）→ LA/RootTowerLength へ（§9.1 の前提）。CompletedTower を
  下ろすと Inputs → Paper の逆転も消える。
- 1 定理だけのつなぎ：Section5/CharacteristicZeroReduction（33）・CompletionReduction（48）・ResidueFieldReduction（48）・ModuleReduction（34）。
  Lemma 5.1 の還元として 1 本にまとめる（§10.5）。

### 10.4 重複

- Cor 2.6(3) が二回：`Section2.cor_2_6_residue_pos`（死んでいる）と `Section4.residue_length_pos_of_lengthAlgebra_values`（主経路）。
  `Paper/Corollary2_6.cor_2_6_pos` は前者の包み。一本に（主経路の方を Cor 2.6 の場所に置く）。
- Cor 2.6(1,2) の `cor_2_6_tor` と Lemma 3.4 の `lemma_3_4` は同じ議論（v = 1 の値に `normalizedLength_tor_of_isWeaklyRegular` を当てる）。
- (2.5) の v = 1 の計算が `ParameterLengthPositivity.parameterQuotient_length_eq_multiplicity`・`LengthAlgebraConsequences`・`Section2/Corollary2_6` の 3 か所。
- Thm 4.7 の `theorem_4_7_K0`、FlatRealization の `symmetricPaperEuler_conjSum_eq_of_flat` は、主経路の `symmetricPaperEuler_conjSum_eq`（SecondComparison）と並行。
- 正値性の二経路（AsymptoticPositivity＋SecondComparisonLowerBound と ApproximationPositivity＋ApproximationSecondComparison）。
- `Core` の private `exists_nat_ringKrullDim` と `PrimeReduction`（§9.2）。

### 10.5 構成の案（内容の名前。論文の番号は docstring に書く）

| 新しいファイル | 元のファイル |
| --- | --- |
| Statement | Statement（Thm 1.1） |
| Section2/ResidueFieldExtension | Lemma2_1 |
| Section2/NormalizationBase | Lemma2_2 |
| Section2/TowerLength | Lemma2_4（Lemma 2.3 の主張は TowerLength・TowerDescent を LA へ移した後に） |
| Section2/LengthAlgebra | Theorem2_5・LengthAlgebraConsequences の (2.6) の部分・LengthAlgebraConstruction の論文の部分 |
| Section2/LengthAlgebra/EqualChar | PerfectQuotientLimit・PerfectKoszulLimit・Perfect* の論文の部分（Thm 2.5 の等標数） |
| Section2/LengthAlgebra/MixedChar | MixedLengthAlgebra |
| Section2/BaseChange | Corollary2_6 の 2 本を一つに（§10.4） |
| Section3/LengthComputation | Lemma3_4 |
| Section3/NormComparison | Lemma3_5・Lemma3_5/{Normalized,Ordinary}（一般部分を外へ） |
| Section4/Setup・EulerComparison・Descent・AsymptoticNormComparison | PaperK0Comparison（Prop 4.5）・UniformRepresentative・SupportedDescent（Lemma 4.6、`sorry`）・SymmetricComparison＋Theorem4_7＋LengthHypotheses＋LengthAlgebraRealization の論文の部分・FlatRealization（変種）・Asymptotic の PaperQuotient（G の 3） |
| Section5/Reduction | CompletionReduction・ResidueFieldReduction・ModuleReduction・PrimeReduction・CharacteristicZeroReduction（Lemma 5.1） |
| Section5/Setup | Core・GaloisNormalization・NormalizationPositivity・SelectedParameterPositivity・ParameterChoice（§5.1） |
| Section5/FirstComparison | Lemma5_2・FirstComparison（c_σ）・NormApplication |
| Section5/ParameterQuotient | ParameterQuotient（5.3・5.4）・ParameterQuotientCM・Preparation |
| Section5/SecondComparison | SecondComparison・ApproximationSecondComparison・ApproximationEuler・ApproximationBetti の論文の部分 |
| Section5/Positivity | Positivity・CoreLengthPositivity・TwistedLengthPositivity・ParameterLengthPositivity・TowerPositivity・（Regular）LengthAlgebraPositivity・ApproximationPositivity |

- ディレクトリ名 Section2〜Section5 は論文の節に合わせて残す（Paper の中に限り C の規約の例外、G の 8 で決定）。Section3/ を新設し、
  トップ階層の Corollary2_6・Lemma3_4・Lemma3_5（と同名のディレクトリ）・Lemma5_2 を節の下へ。
- 名前空間：`Section2`・`Section4`・`Section5` と裸の `SerrePositivity`（Corollary2_6・Lemma3_4・Lemma3_5・Lemma5_2・Positivity・FirstComparison・
  NormApplication）が混在。`SerrePositivity.Paper` にそろえる。宣言の `paper*` 接頭辞（`paperBaseChangeBetti_*`・`ordinaryPaperEulerK0`・
  `paperOrdinaryEulerK0_*`）、`nontrivial_of_section4_quotient`、略称 `φσ`・`Iσ`・`TD` は内容の名前に。PaperK0Comparison の「Paper」も。
- `maxHeartbeats` の引き上げが 16 ファイル 23 か所（2,400,000 が 7 ファイル、1,800,000 が 2、1,200,000 が 1、800,000 が 13）、
  `synthInstance.maxSize 2048` とファイル全体の `backward.isDefEq.respectTransparency false` が Section4・5 のほぼ全部。統合のときに範囲を限る。
- LengthAlgebraConstruction のモジュールの docstring が「等標数の Thm 2.5 は Roberts の引用に依存」のまま（本体の docstring では外れている）。直す。

- **決定（2026-11-01、ユーザー）**：(1) 名前空間の `SerrePositivity.Paper` へのそろえは区切り 1-4 では見送る（宣言名が変わると公理の監査・README の入力の表・
  Inputs の docstring・他のレーンの文書も変わるので、別の機会にまとめて行う）。(2) Section5 の Approximation の 4 本は Paper に残す（同日調査）：ApproximationLowerBound は Paper/Section5/ParameterQuotient（Lemma 5.4 の長さの収束）、MinimalApproximation・SupportedApproximation はその上に立ち、ApproximationHomology が使う MinimalTruncationComparison は論文の TruncationComparison を使うので Paper/Section4 へ移る。Asymptotic へ移すと Asymptotic → Paper の逆転になる。`Paper/Section5/Approximation` にまとめる。ApproximationHomology の主張（Tor の極限から Betti 数の増大条件）は一般的なので、MinimalTruncationComparison の論文に固有でない部分を切り出せれば Asymptotic へ下ろす候補。
  (3) §10.4 の重複は一本にする（主経路で使っている方を残し、論文の番号は docstring に書く）。

### 10.6 共有層へ下ろす一般の補題（第 9 章の 12 本以外）

| 元 | 一般の補題 | 行き先 |
| --- | --- | --- |
| Lemma3_5 | `radical_span_eq_maximalIdeal`、`isKoszulResolution_of_regular` | CA（SystemOfParameters・Koszul） |
| Lemma3_5/Ordinary | `isArtinianRing_quotient_span_of_finite`（LengthAlgebraRealization も使う）、`length_homology_ne_top_of_radical`・`chiOrdHom_of_radical`・`chiOrd_baseChange_koszulComplex` | CA、PerfectComplex/OrdinaryEuler |
| Lemma3_5/Normalized | `lemma_3_5a_lam_finite`（Koszul の有限性） | PerfectComplex/NormalizedEuler |
| Section2/PerfectKoszulLength | 全部（Frobenius・根の段の Koszul の長さ、`perfectionApproximationBaseMap`、一様な冪ねじれ） | LA/RootTowerLength/PerfectKoszul（長さを使わない部分は CA/Perfection） |
| Section2/PerfectKoszulLimit | 帰納極限の同値（未使用）、極限の仮定からの完全化の Koszul ホモロジーの λ の消滅 | LA/RootTowerLength |
| Section2/PerfectQuotientLimit | Hilbert–Kunz 型の極限 λ(D_perf/H)（最後の `…_eq_multiplicity_of_higher_tendsto` だけ Thm 2.5 固有） | LA/RootTowerLength |
| Section2/TowerKoszulLength・TowerLengthOn・CompletedTower | 全部 | LA/RootTowerLength（Restriction・Completed） |
| Section2/LengthAlgebraConsequences | `parameter_quotient_values_pow`（任意の λ での重複度の冪の公式） | LA（か IM） |
| Section2/LengthAlgebraConstruction | `perfectClosure_length_properties_of_higher_tendsto`・`_of_roberts`（等標数） | LA/RootTowerLength/Perfect |
| Section4/LengthAlgebraRealization | `finite_lengthAlgebra_ideal_fg`・`finite_lengthAlgebra_support`・`koszulFinite_/quotient_length_/koszulEuler_of_lengthAlgebra_values`・`koszulEuler_eq_…` | LA（Koszul・Flat） |
| Section4/LengthHypotheses | `algebraMap_injective_of_spectrum_surjective`、`nontrivial_of_section4_quotient`（改名） | CA、LA |
| Section4/UniformRepresentative | `supportedRank_isIdempotentComplete_of_koszul` | Asymptotic（SupportedRankTStructure） |
| Section5/Preparation | `exists_pow_maximalIdeal_map_le` | CA |
| Section5/ApproximationHomology・ApproximationBetti・MinimalApproximation・SupportedApproximation・ApproximationLowerBound | 近似の極限から Betti 数・Euler 標数の評価、極小分解の切り詰め（ApproximationBetti の 2 定理は未使用） | Asymptotic（MinimalResolutionFamily ほか） |
| Section5/FirstComparison | `firstComparison_of_complex`・`_of_resolution` | IM/ResolutionEvaluation |
| Section5/ParameterChoice | `exists_regular_parameters_for_finite_extension` | CA/SystemOfParameters |
| Section5/SecondComparison・ApproximationSecondComparison・LengthAlgebraPositivity | 多くは任意の λ 代数についての抽象的な議論（論文固有の部分は薄い） | Asymptotic の候補（中身を見て判断） |

どれも BS・CLMST に依存しない。未使用：`ApproximationBetti` の 3 つ、`exists_supported_approximation_with_lambdaChi`、
`perfectionKoszulHomologyDirectLimitEquiv`、`towerLengthOn_len`、`lemma_3_5b`、`lemma_2_4_*`（4）、`lemma_3_4`、`theorem_4_7`、FlatRealization の 3 定理。

### 10.7 順序

1. 再エクスポート Tower・MonomialBasis・TowerStage の削除は区切り 0 の追加分。MixedPerfectoid は区切り 2a。
2. 一般の補題を下ろす（§9.2・§10.6）：CA 行きは区切り 1-1、LA・PC・IM 行きは区切り 1-3、Asymptotic 行きは区切り 1-4。
3. Paper の再構成（§10.5）と重複の一本化（§10.4）、名前空間・名前の付け替えは区切り 1-4。BS 依存の混標数の部分（MixedLengthAlgebra ほか）の
   import は区切り 2a の後に確定する。

## 第11章 Inputs・GroupTheory

調査（2026-10-30、読むだけ）。

### 11.1 Inputs/ の中身

`Inputs/` は引用（証明を `sorry` で置く入力）の置き場のはずだが、14 本のうち本物の引用は 2 本だけ。`scripts/make_area_audits.py` が `sorry` を許して
いるのは Inputs/Descent・Inputs/Homotopy/KanQuillen（と Paper/Section4/SupportedDescent・BhattScholze/Inputs/PerfectoidizationInterface）。

| ファイル | 中身 | 扱い |
| --- | --- | --- |
| Descent | `theorem_3_1_K0`（論文 Thm 3.1 の K₀ での帰結 (3.2)、Land–Tamme の cdh 降下。`sorry`）。Paper/Lemma3_5 が使う。KST のレーン（k-theory-kst-route.md の段 1a）が解消する予定 | 残す（本物の引用）。名前空間は `SerrePositivity` のまま（`Inputs` ではない）。`K0Supported` の型で書かれている（§4.2.3、G の 6） |
| Homotopy/KanQuillen | `kanQuillen_model_exists`（Hovey Thm 3.6.5、`sorry`） | ∞ 基盤の側。主定理の閉包の外（verify で確認済み） |
| Homotopy/ResolutionHom・SimplicialLevel | KanQuillen の適用（`sorry` なし）。scripts の check だけが import | ∞ 基盤の側 |
| DifferentialGraded/（README だけ） | dg の引用の台帳（採用 0 件） | ∞ 基盤（dg）の側 |
| IntersectionTheory | `regularResolution`・`intersectionVanishing` は `SerrePositivity.regularResolution`・`intersectionVanishing_of_adams` の別名（証明済み） | 削除。IM/FiniteExtension・IM/Devissage は `intersectionVanishing_of_adams` を直接使う。IM/Additivity の import を外す（Adams の一式を引き込んでいる）。FiniteExtension・EqualCharZeroPositivity の「未証明の定理」という古い docstring を直す（§5.2 の 6、§5.8） |
| CohenNormalization | `exists_cohen_gabber_normalization`（CA/CohenGabber）・`exists_cohen_normalization_mixedCharacteristic`（CA/Witt）の包み。利用は Paper/Section2/Lemma2_2 だけ | 削除し Lemma2_2 から直接呼ぶ。文献（Kurano–Shimomoto Thm 1.1、Stacks 0323）は CA 側の docstring へ |
| ResidueFieldExtension | `exists_complete_flat_local_extension_of_residueField`（CA/ResidueFieldExtension/General）の包み。利用は Paper/Section2/Lemma2_1 だけ | 削除し直接呼ぶ（EGA 0_I 6.8.3、Stacks 03C3 は CA 側へ） |
| PerfectoidTower | `completedTower_isIntegralPerfectoid`（CA/RootTower の定理の包み、CLMST Example 2.4.2(1)）。利用は Paper/Section2/LengthAlgebraConstruction | 削除し直接呼ぶ |
| CLMST | CLMST の Prop 4.0.10・Cor 4.0.4・Prop 4.0.14 の 3 つの包み。Paper/Section2/* を import していて（Inputs が Paper の上にある）、利用は Paper/Section2/MixedLengthAlgebra だけ | 削除し MixedLengthAlgebra から `CLMST.*` を直接呼ぶ（CLMST/Inputs/ の解体、§8.3 と同じ方針） |
| Perfectoidization | BS Thm 1.17(1) の包み（`BhattScholze.exists_perfectoidization_of_finite`）。利用は CA/Perfectoidization だけ（`.choose` 4 回） | BS のセッションの管轄。CA/Perfectoidization を BS 側へ移すとき（§2.8・区切り 2a）に合わせて扱う。CA → Inputs → BS の逆転の原因 |
| LengthAlgebra | `lengthAlgebra_base_values(_one)`（約 20 行、証明済み、引用なし）。`_one` の利用は Paper/Corollary2_6 だけ | Paper/Corollary2_6 か LengthAlgebra へ移す |
| RegularLocalRing・RegularParameters・Unmixedness | import だけの殻（CA の RegularLocalRing/Basic・Unmixedness の再エクスポート）。importer はルートだけ | 削除（区切り 0 の追加分） |

整理の後、Inputs/ に残るのは Descent（論文・KST のレーン）と Homotopy/（∞ 基盤）だけ。Homotopy/ は ∞ 基盤の Inputs へ移すのが自然。
Mathlib にはどの主張もない（コーエンの構造定理、Kan–Quillen のモデル構造、perfectoid 化、K 理論の降下）。

### 11.2 GroupTheory/

| ファイル | 中身 | 利用者 | 扱い |
| --- | --- | --- | --- |
| ConjugateSum（59 行） | `conjSum_eq`：G の軌道和 Σ_g φ(g•y) が、f(K) 上で一致する加法写像 φ, ψ について等しい（G 不変元の正の倍が f(K) に入るとき）。`conjSum_eq_of_base_formula` | CategoryTheory/EulerComparison だけ（その先は Paper/Section4/SymmetricComparison・LA/Comparison）。論文の層 | 名前が内容と合わない（共役類ではなく軌道の和）。`orbitSum_eq_of_descent` などに改名し、EulerComparison（§1.2.1 の Euler）か Paper 側の比較のファイルへ吸収。CT → GroupTheory の逆転（B）も消える |
| Coxeter/（TypeA 955・FirstToLast 90・PermutationInduction 28・InvolutionRelations 37） | A_n 型 Coxeter 群 ≅ Sₙ₊₁（`typeAEquivPerm`、挿入ソートの標準形）、隣接互換による置換の帰納法、`firstToLastPerm`、対合の関係式。ArxivFormalization から移植 | すべて ∞ 基盤の側（CategoryTheory/Monoidal・EInfinity/Operad・IntervalCuts・Spectra/SymmetricSequence） | ∞ 基盤の側へ渡す（refactoring-infinity-r2.md の R67 が Monoidal の利用者の再分類を計画済み） |

Coxeter の Mathlib との重なり（∞ 側への申し送り）：`permutation_induction_right` は `Equiv.Perm.mclosure_swap_castSucc_succ` と
`Submonoid.induction_of_closure_eq_top_right` から出る（確度高、TypeA の 955 行が不要になりうる）。`adjacentTransposition` は `swap i.castSucc i.succ`。
`shiftPerm`・`firstToLastPerm` は `Equiv.Perm.decomposeFin`・`finRotate`・`Fin.cycleRange` と重なる（確度中）。A_n ≅ Sₙ₊₁ は Mathlib にない
（`CoxeterMatrix.A`・`CoxeterSystem` はあるが対称群との同型はない。確度高）ので、使うなら提出候補。

### 11.3 層の逆転（B に追加）

- CA/Perfectoidization → Inputs/Perfectoidization → BhattScholze（区切り 2a で CA/Perfectoidization を BS 側へ）。
- Inputs/CLMST → Paper/Section2/*（Inputs を消せば解消）。
- IM/Additivity → Inputs/IntersectionTheory → IM/AdamsVanishingAll（Inputs を消せば解消）。
- CategoryTheory/EulerComparison → GroupTheory/ConjugateSum（吸収で解消）。CategoryTheory/Monoidal → GroupTheory/Coxeter は ∞ 側の中の依存。

### 11.4 順序

1. 殻 3 本（RegularLocalRing・RegularParameters・Unmixedness）は区切り 0 に追加。
2. IntersectionTheory・CohenNormalization・ResidueFieldExtension・PerfectoidTower・LengthAlgebra の包みの解体は区切り 1-1（CA・Paper の利用者の
   書き換えだけ）。IntersectionTheory は IM の作業（区切り 1-3）と同時でもよい。
3. Inputs/CLMST の解体は Paper の再構成（区切り 1-4）。Inputs/Perfectoidization は区切り 2a（BS のセッションと調整）。
4. ConjugateSum は区切り 1-1（CT のトップ階層）。Coxeter と Inputs/Homotopy・Inputs/DifferentialGraded は ∞ 基盤へ渡した（伝達文 §6）。
