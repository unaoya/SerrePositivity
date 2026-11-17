# R2-E 計画検証：不整合と修正案（2026-10-27、R-V）

判定：**既存の固定入力成果は保存できるが、進捗表の数式・所有・完了表示と正本の適用範囲を改訂する必要がある。**
対象は foundations-progress、infinity-core-* 20 本、kst-lanes 直下 16 本（計 37 計画）と foundations／KST 正本等。
検査開始時 HEAD は `688a49e63433e06ef6eb21625cd44e30b90902a3`。稼働中 checkout の未コミット成果も区別して読んだ。
本報告と [R2 分担表](stage-i/refactoring-infinity-r2.md) §2 の R2-E 行以外は変更していない。以下の修正・移動は提案で、未実施。

## 1. 一枚の不整合一覧・修正指示

| 優先 | 根拠（ファイル・節／検査時行） | 不整合／判定 | 修正案・担当先 |
| --- | --- | --- | --- |
| 高 | foundations-progress:280、F2-St §A・追補3c/3d、L10「延長分」 | 進捗表の採用文は `Ind_κ(C)^κ/C`、connective K の fiber 列から delooping、普遍性だけで局所化性が出るように読める。F2-St の修正と不一致 | コーディネータが採用文を下記 §2 の定式化へ置換。元文は日付付き設計履歴へ保存 |
| 高 | foundations §1・§2 K-7、KST §13 決定16、L1:112・187、L10:3–7 | dg による **対象供給** と全高次 **関手性** の制限範囲が未分離。L1 の「安定∞圏上の既存成果は補助」「新たな K は厳密 dg 限定」を全工程へ適用すると新設計を禁止する | 決定16に追補を新設し「LT の dg 入力・既存 K は保持。延長分は StableInfinity／perf 上で構成し ν へ引き戻す」と明記。L1 は既存 dg 実装の範囲に限定し、新 K∞ の担当・受入条件は別項目にする |
| 高 | foundations-progress:318、L10:28、D-S §2026-10-27 の再分担、D §∞評価 | 旧 c4 の厳密全作用供給待ち・ε 整合 Hom の中継待ちと、その経路を追わない決定が併存 | c4 は「凍結・旧条件付き入口保持」、D/D-S 旧依頼は「新設計により失効」と明示。L10 冒頭を現状の正本にし、旧供給待ちを再発注しない |
| 中 | foundations-progress:303–312 と L3 引き継ぎ | K-6 親項目は [x]、b は [ ]。L3 は b の無条件化を報告し `Relative.k6Fibration` が実在 | b を bcba4d552／L3 に照合して完了へ更新。K-B2 の終了項目も現所有へ畳む。旧固定 kSpectrumMap 右辺への射比較まで完成とは書かない |
| 中 | foundations-progress:136・138、P-s 冒頭 | P-12「保留」、P-14「取り消し」が [x]。数学的完成と管理上の終了が混在 | P-12 は未完・第II段、P-14 は取消としてチェック欄外へ。Ind/X の代替経路による親完了は正当で、凍結 a③/a④ を完成に変えない |
| 中 | foundations-progress:121–132、P-d 引き継ぎ | 対ごとの全関手圏双対は完成、全 Pr 双対は未完で整合。ただし e6-6 の監査・引継ぎは旧全体工程と局所完了が混在 | 対ごとの監査・引継ぎは完了、全 Pr は第II段に分離。「P-d 完了」を全 Pr 完了と読ませない |
| 中 | foundations-progress:296、D:141、L9 冒頭、L9b/c・L10 所有節 | K-B が NonConnective まで所有する旧見出し、Sp の広域所有と Sp-2/3 の排他的所有が重複。D の広域所有も D-S 等の新規葉を包む | 現所有表を一つにする：K-B＝Fibration 閉鎖、K-B3＝NonConnective、Sp-2＝D3 新葉/独自集約、Sp-3＝S3 新4葉/監査、K-S•＝SConstruction（Cofinality 分担を除く）、D/D-S の除外ディレクトリを列挙。旧見出しは履歴へ |
| 中 | L1:11・99、L9c §供給依頼、progress:269–276 | L1 の F1 延長依頼「未達」は自レーン代替で接続済みの過去記録。現在の Sp-3 待機は K-S• ③ の実長方形・三認証 | 過去の未中継事故は archive、現行依頼表は供給者・受給者・型・送付状態・公開名の5欄にする。K-S•→Sp-3 の三認証は未供給のまま維持 |
| 中 | L9b §286以降、L9c §工程 | Sp-2 の段比較・判定定理は存在するが補正の恒等性／BF 比較は未証明。Sp-3 の [x] は条件付き消費骨格と監査のみ | d3/hΩ/sp_isStable、s3 と最終 s5 を未完のまま維持。L10 の「Sp-2 s3」は **Sp-3 s3** へ修正 |
| 中 | foundations-progress:285・291・294、F2-St §D | 旧完成予測10-28〜31・旧 I-4 の一括完成条件と、延長設計184〜368時間（K本体別枠）が併存 | 旧日程は履歴扱い。固定入力成果／∞延長／I-5／I-6 の受入条件と依存を別々に再固定。工数評価を確定納期にしない |
| 低 | KST §12「LT の⊙を使わない」、§9/§13決定2・6 | 決定16で上書きされた旧経路・暫定(b)が本文に残る | §13 決定15・16を保持し、旧調査・旧決定の適用終了を表示。現行概要は LT／BGT(a) で統一 |
| 低 | L1/L2/L4/L5/L6/L7/L8 の末尾記録リンク | `archive/L*-log.md` は kst-lanes/archive を指し不在。実ファイルは formalization-plans/archive に存在（7件） | 各所有者が `../archive/L*-log.md` に修正。下記圧縮の際も相対リンクを検査 |

## 2. 決定15・16への追補案（本文未変更）

- 決定15は L8 の Tot・homotopy limit の実模型と整数π、ModelCategory 仮定の排除を規定する。dg 入力制限そのものを定める決定ではない。新設計でもこの制約を維持する。
- 決定16の LT／dg 増強による環・gluing・商の具体的供給は維持。**K の延長分の関手性だけは正しい写像空間を持つ∞圏で構成する**。対象別 dg 比較は自然比較を自動供給しない。
- `S=StablePerfInfinity`、包含 `J:S→StableInfinity`、`ω<κ` 正則を固定。`Fκ(C)=(Ind_ω C)^κ`、`Σκ^raw(C)=Fκ(C)/C`、`Σκ^perf=Idem∘Σκ^raw`。`Ind_κ(C)^κ≃Idem(C)` の既存比較を cone と取り違えない。
- 既存 StableInfinity は安定対象の圏で、冪等完備性は定義にない。全域登録には全高次の完備化 `P:StableInfinity→S` と raw 列の perf-exact 列への移送が必要。ν が既に perf へ因子化する場合も、その実作用と比較を渡す。
- `K∞:StableInfinity→Sp` と `θ:K∞J⇒Ω K∞JΣκ^perf` を全自然変換として構成する。指定 K-6/BF 射への回収と raw→perf 比較を保持し、θ 自体を一般の同値と仮定しない。
- `Seqκ:S→Fun(N(ℕ),Sp)` の n 段を `Ωⁿ K∞(J(Σκ^perf)ⁿ C)`、遷移を `Ωⁿ θ((Σκ^perf)ⁿ C)` とし、`Knc=colim_ℕ∘Seqκ`。固定 A の既存 BF 図式と全反復構造射を含む FunctorIso を作って対象別比較を得る。最終登録は `ν≫P≫Knc`（perf 因子化がある場合は同値な制限）。
- 局所化定理は別工程：Fκ/Σκ の exact 列保存、connective K の必要な比較、反復での欠損消去、Sp 余極限・fiber の交換、Morita／完備化・通常 filtered 余極限との整合を証明する。商普遍性・swindle だけで Knc の fiber 性を宣言しない。
- [F2-St §A・追補3](stage-i/infinity-lanes/infinity-core-stability-functoriality.md) を設計仕様として参照する。一般底 Cat∞ straightening と全 Pr 双対性は未完成であり、Ind 専用の普遍性族化を使う場合も共有境界・全 n の整合を別途証明する。

## 3. R 候補の網羅と中継先（§3への追加はコーディネータに委ねる）

R26〜R36 は既存11候補を収載するが、全候補の台帳ではない。次を追記または既存候補の明示的な小項目にする。
本数は検査時の SerrePositivity 配下 Lean の **直接 import 利用元数**（推移閉包・scripts は含めない）。移動時は再計測する。

| 未収載・参照不足の対象 | 処置案・影響 | 中継先／検証・工数案 |
| --- | --- | --- |
| Derived/FunctorIsoConstantEdges(6)、Stable/PosetSubtypeNerve(7)・FinitePosetNerve(5)、HomotopyLimits/FullSubcomplexConeLift(3)・FullSubcomplexLimitReflection(3)・EmptyCone(5)、Stable/FunctorFiniteLimits(5) | Core への移動候補。progress の R 行にはあるが番号なし | R2-A/B、各閉包を再確認し move_module＋verify。各0.5〜2h |
| Derived/PinchedSliceCompositionRealization(4)・ConstantEdgeFamily(9)、F2/Presentable/CoconeFunctorUnitPrism(3)、HomotopyLimits/CosliceShapePushout(6) | Core/PinchedHom または F1B。大きな閉包を単純に Core 扱いしない | R2-A/B、分割要否を先に判定、各2〜8h＋verify |
| Derived/DGAlgebraDerivedInfinity(9) の DGAlgebraPoint・enrichment | 一対象 dg 圏の一般部分だけ DifferentialGraded/Category へ分割 | R2-B、公開名・型を保存、2〜4h＋verify |
| LocalizingInvariants/GeneralLocalization〜ParametricDiagramGluing | 一般局所化を F1B 等へ分離。progress の「12本」は列挙すると **13本** | R2-A/C、正本の所有移管も同時に確定、閉包・利用元を再計数、4〜8h＋verify |
| Stable/ExcisionRepresentableLimits(3) の SpaceInfinity 有限極限供給 | HomotopyLimits/Core の軽い証明へ付替え。単なるファイル移動ではない | R2-A、型・数学的内容を保存、4〜16h＋verify |
| D2 計画:25 の F2.laxPullbackCospanIsoEquivalence と関連 F2 10葉 | 実所在は F2/CatInfinity、新葉は D2 集約のみ登録。F2 集約・監査へ登録候補 | R2-A/D、登録先と閉包循環を検査、1〜3h＋verify |
| L3 §R候補の14葉（証明核を含む） | R33/36 へ明示リンク。ConnectiveFibrationTheorem 等は主定理内部で必要、削除・一律凍結不可 | R2-B/C、import と宣言消費の両方を分類、4〜8h＋verify |
| P-d 全 Pr 双対・P-12 compact 判定（「第II段／R」） | **数学的な新規証明**。公開名・型を保存する R 窓には入れず第II段へ。新設計が必要とする部分のみ別途再発注 | コーディネータ／F2-St。R 調査の完了やコード移動と混同しない |

R26/27 は既知の逆向き辺、R28/29/30 は統合、R31 は Ind-π、R32/33 は D/D-S 反例・凍結、R34 は E2-S(8)、R35 は BS、R36 は未登録を既に覆う。
R2-B の DG→SConstruction 一般層、HomologicalAlgebra→CommutativeAlgebra、R21/R4/R5/R10 の持越しも、担当表だけで終わらせず候補番号への対応を付ける。
Sp-3→K-S• の三認証依頼は現行計画に「チャットでも通知済み」、L1/L3/L10 の現行未送付欄は「なし」。**新たな未中継依頼の存在は文書から確定しなかった**。
チャット配達履歴そのものは未検査。D-S の旧中継待ち、L1 の旧 F1 未達は失効／代替済みとして閉じ、現在の供給待ちと区別する。

## 4. 300行超8計画の圧縮案（行範囲は検査時、実移動なし）

全8本は依頼記載どおり計4,226行。保存先は原則 formalization-plans/archive、現行に要約・受入条件・参照リンクを残す。

| 現行（行数） | archive へ移す範囲・保存先案 | 現行に残す内容／目標 |
| --- | --- | --- |
| foundations-progress (365) | 各 [x] 行内の時系列追記、:283–292 の旧再編・見通し、:353–365 確定済みを `foundations-progress-through-2026-10-27.md` に保存 | 全固定項目のID・状態・証拠コミットは残す。:280–282 は訂正した新決定、:294 は改訂した受入条件に置換。状態表＋依頼表で180〜250行 |
| perfectoidization-interface (1090) | :245–314 §5、:418–1090 の工程表・長い型記録を `perfectoidization-interface-types-2026-10-27.md` へ。§4:201–244 の草案も同付録へ | §1〜3・§6・§7の責務要約、現在の唯一入力E3・二旧入口の消費先・未完比較を保持。原文照合と草案／実宣言の区別を残して250〜290行 |
| k-theory-kst-route (480) | :50–218 §2調査、:341–428 §6〜10 の旧工数・未決・紙検証、:440–448 §12旧変更履歴を `k-theory-kst-route-pre-lt-2026-10-27.md` へ | §13の決定15・16を含む決定台帳は保持（上書き済み行を明記）。現行LT経路・レーン表・受入条件・新設計追補を再編集し250〜290行 |
| dg-theory-u12e-general-inventory (639) | :102–639 全519モジュール台帳と最終検証を `dg-theory-u12e-general-inventory-table.md` へ | :1–101 の分類・再現手順を基礎に、固定コミット・未受入条件と付録参照を残して110〜140行 |
| L4 (347) | :157–216 接続点詳細・旧紙検証、:307–321 共通検証手順を既存 `archive/L4-derived-geometry-log.md` の日付節へ | 引き継ぎ・層定義・D_qcと厳密降下の区別・T1〜T3・係数忘却の残件を保持、260〜290行 |
| L7 (340) | :135–176 既存基盤棚卸し、:282–294 紙検証詳細、:304–321 保存手順を既存L7 logへ | 現在地・一般平坦化未完・L7cのK非依存境界・決定を保持、260〜285行 |
| L8 (352) | :122–162 原典／既存型の詳細、:186–218 の旧草案を既存L8 logへ | 引き継ぎ・Main/Auxiliary・最小公理(1)の現仕様要約と(2)〜(8)の残件・決定15を保持、275〜295行 |
| L11 (613) | :31–240 の旧群ホモロジー・pro検証を `L11-paper-pre-lt-checks.md`、:384–613 S1型草案を `L11-K0-interface-draft.md` へ | :1–30現在地をLTに更新。§5/6/11〜14の必要部分・S1要約・草案未コンパイルを残して230〜280行 |

範囲移動は各所有者が実施し、内部アンカー・相対リンク・重複する「次の一手」を更新する。履歴を削除せず、旧案が現行の規範に見えない見出しを付ける。

## 5. 照合証拠と検査の限界

- 37計画の16進コミット参照を抽出し、484個の異なる参照すべてを `git cat-file -t` で commit と確認。
- [x] 行の underscore を持つ識別子候補292個を現 Lean ソースと検索照合：288個が見つかる。残る3個は scripts の監査名（audit_infinity_f2_exchange／audit_f2_ind／audit_einfinity）、1個は数式略記 fib_Sp。欠落公開名とは判定しない。これは字句検査であり全宣言の型・仮定の証明ではない。
- 主要入口は定義箇所も確認：`F2/Ind/CoherentFiniteLimitExchange.indFiniteLimitExchangeInput`、`Ind/Stability.ind_isStable`、`Compact/CompactIndEquivalence.compactIndEquivalence`、`Presentable/Duality/PairDuality.presentableAdjointFunctorEquivalence`、`F1/Diagrams/TriangleNativeExt.nativeTriangle_ext`、`Fibration/Relative/ConnectiveFibration.k6Fibration` と非負比較・懸垂構造射、`SConstruction/Cofinality/Thomason.kSpectrumMap_cofinality`。
- K-7 の `FixedInput` と `InfinityComparisonTarget` は HEAD 688a49e63 に保存済み。後者の `DGKInputCalkinPresentation` は構造体、`DGNonconnectiveSequenceComparisonTarget` は指定D∞への FunctorIso の型で、存在定理ではない。固定Aの実余極限・非負比較の公開と全入力上の局所化登録を分ける。
- `LocalizingInvariants/StableCategories` の StableCategory は安定性のみ、`StableInfinity` はその coherent nerve。`IsVerdierSequence.kernel` は元の essential image との一致を要求することを宣言型で確認。raw/perf と thick 性の注意はこの型に基づく。
- 全37計画のローカルMarkdownリンクを検査して上記7件を検出。ディレクトリの実在と主要入口の所属を照合した。所有はファイル配置だけでは決まらず、最新の分担節を優先する。
- ビルド・公理監査の数値は各コミット／計画の報告で、今回再実行していない。コード無変更の計画検証であり、全 [x] の数学的妥当性・全コミットでのビルド成功を認定する報告ではない。
