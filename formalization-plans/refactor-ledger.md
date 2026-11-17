# リファクタ候補の台帳

作成：2026-11-12（段階 II の調整役）。決定：ユーザー（11-12、リファクタ候補はノートではなく形式化の側で管理し、扱いは調整役が判断する）。

この台帳が**リファクタ候補の状態の正本**。勉強ノート（`exposition/ja/bs/` の BR、`exposition/ja/infinity/` の R）には今後リファクタ候補を書かない。ノートを書いていてコードの問題に気づいたら、事実を `research/` にまとめ、ユーザーから調整役へ伝える。

- 取り込み元：`research/bs-refactor-audit/`（BR1〜BR33、ba24dceb6）、`research/infinity-refactor-audit/`（R 番号、同）。囲みの原文はそれぞれの `box-texts.md`。ノートにしかなかった調査（R8 の重複、R58 の Yoneda の閉包）は `research/infinity-refactor-audit/r8-duplication.html`・`route-yoneda.html` に写した。
- ∞ の R 番号の**中身**の正本は従来どおり `archive/stage-i/refactoring-infinity.md` §0 の索引から辿れる文書（R1〜R79）。ただし §0 の状態欄とパスは 10-30 のままで古い。**状態はこの台帳を正とする**。
- 扱いの語：**閉**（実施済み、または前提が変わり不要）／**B3**（一括レーンの凍結の一晩で行う、`stage-ii/citation-attributes.md`）／**計画**（指定の段・束で行う）／**保守**（段階 II の E3 の sorry 0 の後の保守の束。主定理の経路に乗らないコードの整理）。新しい候補は R80 以降・BR34 以降の番号で足す。

## 1. BS（BR1〜BR33）

| BR | 提案（一行） | 扱い | 理由・行き先 |
| --- | --- | --- | --- |
| BR1・2・3・9・20・27・28・33 | — | 閉 | 実施済み（根拠は監査の README） |
| BR30 | Thm 7.14 の一段の拡大を原典に揃えるか | 閉 | D38（揃えない） |
| BR10 | Variants の重複の削除 | 閉 | 10-26 のユーザー決定（Variants は残してまとめる）。重複する定理の対（Auxiliary:1541 と Tower:1172、RootedExtension:1584 と Tower:1463）の整理は BR13 と一緒に保守 |
| BR11 | 届かない照合と旧経路の削除 | 閉 | 10-26 の決定で PowerRootEnvelope に残し、root から届く |
| BR16 | Fontaine 比較の正則版の枝を消す | 閉 | **既存の決定を優先**：refactor-plan.md 203〜205 行、10-30 のユーザー決定（Fontaine 核の分離性の連鎖を正則版の仮定 `IsHausdorff (ker θ)` のために残す）。単射性の部分の独立は BR17 と一緒に保守 |
| BR18 | 完全 prism のテンソルの枝、標数 p の特殊化 | 閉（標数 p）／保守（テンソル） | 標数 p は BS-W11 で使われるようになった。テンソルの枝（`Prism/Tensor/PerfectPrismResidueTensor`、11 宣言とも外部参照なし）は保守で削除を判断 |
| BR31 | Prop 8.13 環版を A7 の導来版の系に | 計画 | `stage-ii-second-half.md` の 5∞-8（A7） |
| **BR26′** | 共通基盤から BS への新しい逆向きの import 2 本 | **B3** | `CommutativeAlgebra/KoszulRegular/Powers` → `BhattScholze.Andre.OrdinaryRoots.MonicRelation`（W15）、`HomologicalAlgebra/DerivedCompletion/PrincipalCompletionUniformBound` → `BhattScholze.Andre.Transfinite.Colimit`（W17）。使う補題を共通基盤へ移すか、importer を BS へ移す。5 層の規則（KL-W1）の層違反として B3 の静的検査に含める |
| BR14 | `Andre/PowerRootEnvelope/Audit/` の監査 4 本を scripts/ へ | B3 | ライブラリ内に `#print axioms` を置かない。B3 の配置案の「保持」を改め、scripts/ へ移す（root から届かないので利用側なし） |
| BR19 | `Prism/Residue/PrismaticResidue`（原典に項目のない道具）の置き場所 | B3 | B3 の BS の配置で、使う側の節（または CommutativeAlgebra）へ |
| BR32 | `Delta/DividedPower/`（23 本）を原典の項目ごとに分け、生の包を Division/Prism の近くへ、分冪代数を CommutativeAlgebra へ | B3 | B3 の BS の整理に含める（`Delta` は「保持」から、DividedPower の下位分割へ）。分冪代数の一般部分の CommutativeAlgebra への移動は層の規則に沿う |
| BR25 | docstring の工程ラベル（G 系・B4-x・A1-b・F4〜F7・N3、33 ファイル）を数学の言葉に、書式の欠け（14 本） | B3 | 文献の属性の付与で同じファイルの docstring を触るので、同じ回にラベルを原典の番号へ置き換える |
| BR8 | どこからも使われないモジュール（今 60 本） | B3（調査）／保守（削除） | B3 の片付けの調査に含め、宣言単位で利用者がないことを確かめたものを一覧にする。削除は保守 |
| BR4 | 自由 δ 環の ℤ 版と相対版を一本に | 保守 | 経路に乗らない重複 |
| BR5 | p 正則版 `isDeltaHom_frobeniusLift` を一般版で置き換え | 保守 | 同上 |
| BR6 | pd 包の同型の三重構成を一本に（W15 で多変数版が別に増えた） | 保守（優先） | 重複が増えている。`principalDPFactorialEquiv`・`dpFamilyFactorialEquiv`・`freeDPFactorialEquiv`・`frobeniusDivisionFactorialEquiv`・`pDivisionFactorialBaseEquivOfDividedPowers` を一つの一般形から |
| BR7 | 根の関係とモニック関係の並行ファイル群 | 保守 | |
| BR12 | 条件付き版・重複系列・旧い適用形の残り | 保守 | 旧い適用形 2 本（監査だけが使う）の扱い |
| BR13 | 手で繰り返す証明の型を汎用補題に（商の導来 H⁰ 6 回、perfectoid の prism 表示 5 か所） | 保守（優先） | (b) は W17 の `exists_boundedPerfectPrismPresentation` があるので置き換えが容易 |
| BR15 | Lemma 3.9 の p 進完備化系と除算の枝を消し PD 版に一本化 | 保守 | 監査だけが使う |
| BR17 | 「反復除算と分離性から単射」の 2 か所、「p は単元でない」の共通化 | 保守 | BR16 の単射性の部分と一緒に |
| BR21 | `IsPerfectoidization.hom_ext`・移送補題、複製の置き換え | 保守（優先） | 小さく効果が大きい |
| BR22 | 底変換と三角図式の共通化、テンソルの二つの模型の一本化 | 保守 | 調査から |
| BR23 | Prop 8.13 環版の公開、`isIntegralPerfectoid_of_ringEquiv` の移動、互換 alias | 保守 | 環版の扱いは BR31 で決まる |
| BR24 | Almost/ の supported quotient を `IsAlmost*` の言葉で | 保守 | |
| BR29 | Thm 3.10 を一つの入口に、圏同値 | 計画（圏同値）／保守（入口） | 圏同値は a5-design G-A5-4（drafts `A5/PerfectSite`）で ⑤∞ |

## 2. ∞ 圏（R 番号）

中身の正本は `archive/stage-i/refactoring-infinity.md` §0 の索引。ここには状態と扱いだけを書く。§0 の「中身が正本と同じ」R（監査 README §1 の列挙）は、下の表に挙げないものは §0 の状態のまま。

| R | 扱い | 理由・行き先 |
| --- | --- | --- |
| R1 | 閉 | KL-W1（11-12）が Kerodon/・HTT/・HA/・Project/ の配置に置き換えた |
| R6・R9・R18（三つ目） | 閉 | 置き場所の案は KL-W1 の配置が置き換えた |
| R64 | 閉 | KL-W1 の配置（Kan・pointed は InfinityCategories の中） |
| R4・R5（後半）・R10 | 保守 | 主定理・補題の分離、双対化、計算規則の統合。中身は `research/infinity-refactor-audit/README.md` §2 |
| R8 | 保守（優先） | 宣言単位の重複（同一本体 275 群、余分なコピー 364 個・約 3,400 行）。調査は `research/infinity-refactor-audit/r8-duplication.html`。B3 の Project の整理と同じ道具（KL-W1 の改名と保存比較）で、B3 の後に別の回で行う |
| R21 | B3 | docstring の書式（BR25 と同じ扱い）。文献の属性の付与と同じ回 |
| R58 | 閉（記録のみ） | Yoneda の閉包の調査。`research/infinity-refactor-audit/route-yoneda.html` に写した。R27・R37 に統合して扱う（§0 のとおり） |
| R50（`IsVerdierPair`）・R53（`IsThick`・`thickClosure`）・R62（`fraction_ho_localization` の公開）・R52 の残り | 計画（K の再開） | Verdier 商と厚い部分圏は K の基盤（① ∞ 中核、`k-restart-draft.md`）。どれも実施・取りやめの記録がなかったので、ここで「K の再開の ① の段 0 で扱う」と決める |
| R72 | 計画 | cleanup-list L3（M16、段 G）のまま。f-02 の見込み（12 本の分割で消える）は外れた |
| R80（新、旧ノートの R27 の別の意味） | 保守（要らないかもしれない） | 写像空間の模型 3（Fun(Δ¹,C) の fiber）を定義として足し、pinched 模型との同値を示す案。Kerodon の地図（§4.6）と照らして要否を判断 |
| R81（新、旧ノートの R54 の別の意味） | 保守 | `KanHomotopyGroup X n` が π_{n+1} を表す添字の名前の見直し |

## 3. 保守の束の時期

段階 II の E3 の sorry 0（5∞-9）の後、または B3 の後に人手が空いたとき。優先は BS の BR6・BR13・BR21 と ∞ の R8（どれも重複の削減）。各回は KL-W1 の道具（改名表、保存比較 v3b、追従の collect/rewrite）を使う。

## 4. 作業項目（旧 BS ノートの「形式化の課題」T2・T3、11-12 夜に取り込み）

原文は `research/bs-notes-tasks/README.md`。状態は Prisms の地図（`research/bs-coverage/items.csv`）で照らした。

| 項目 | 内容 | 状態 | 扱い |
| --- | --- | --- | --- |
| T2-0 | 一般のテンソル積への δ 構造（Rem 2.7） | 地図の 2.7 は proved_special（direct limit の δ 構造） | 計画：テンソル積の版は A0 の prism の余積で要るか ⑤∞ の 5∞-2 で確かめる |
| T2-1 | Lemma 2.38 の r 元版 | 済（W15 K1、2.38 proved） | 閉 |
| T2-2 | Cor 2.39 の一般形 | 済（W15 K1、2.39 proved） | 閉 |
| T2-3 | Def 2.42・Lemma 2.43・Cor 2.44 の離散版 | 2.42 は済（W15 K3）、2.43・2.44 は design_only | 計画：E3 の経路で要るかを ⑤∞ で確かめる（D20 は 2.42 だけを使う） |
| T2-4 | Ex 2.21 | 済（W15 K2） | 閉 |
| T3-1 | Lemma 3.6（φ(d) が distinguished） | 地図の 3.6 は none（目標に不要） | 閉（不要） |
| T3-2 | Lemma 3.7 (2)〜(4) | 済（W15 K4、特別な場合） | 閉 |
| T3-3 | Ex 3.4 | 済（W15 K2） | 閉 |
| T3-4 | Prop 3.13 の一般形 | D21 で変数の場合だけ（W15 K4）。一般形は不要 | 閉 |
| T3-5 | Lemma 3.5 の後半（δ 射で prism になる判定） | 地図の 3.5 は proved_special | 計画：A0 の Čech 脈体の各項で要る形か 5∞-2 で確かめる |

## 5. ∞ のノートの片付けで分かったこと（`research/infinity-refactor-audit/README.md` §6、box-texts.md の付録）

| 番号 | 内容 | 扱い |
| --- | --- | --- |
| R82 | 局所化の延長の二つの版：`localization_extension_exists`（Project/HomotopyDiagramComparison/LocalizationExtension:25）と `IsLocalization.exists_extension`（Kerodon/AdjointFunctors/Localization/UniversalConsequences:36） | 保守（R8 の重複と一緒に） |
| R83 | ∞ の一般論が KST（Spectra の Tower* 26 本、SConstruction の Necklace* 45 本、LocalizingInvariants、Fibration の Verdier 分数）・EInfinity/SimplicialLocalization・HomotopicalAlgebra/Simplicial に残る | 計画：KST の分は K の再開の段 0、EInfinity・HomotopicalAlgebra の分は保守（KL-W1 の改名表がこれらを対象にしていないので、移すときは新しい改名表を作る） |
| R84 | `Kerodon/KanComplexes/HomotopyGroups/PointedKanWhitehead.lean` の空の `namespace SerrePositivity.KST.Spectra` と、それを open していること | B3（小さい片付け） |
| R85 | 同じ名前 `pinchedHom` が SSet 版（MorphismSpaces/Basic）と dg 版（PinchedHom）にある | 保守（名前を分ける） |
| R86 | 「安定なら有限極限・有限余極限を持つ」（HA Prop 1.1.3.4 の必要性の向き）の一般の安定 ∞ 圏の instance がない | 計画：③ か ⑤∞ で要る箇所が出たときに足す（今は関手 ∞ 圏などの個別の版で足りている） |
| — | HA Cor 1.4.2.27（Ω による安定性の判定）は `isStable_of_loopEquivalence`（HA/StableInfinityCategories/LoopEquivalenceStability:20）としてある。計画の「未着手（D-7）」は古い | 閉（記録の訂正） |
| — | 06 章：交換定理（HTT 5.3.3.3）の作業量（2 万行を超えて未完成）の記録 | 記録のみ（R8・R10 の背景） |

## 6. BS ノート本文の書き直しで分かったこと（`research/bs-refactor-audit/notes-update-facts-2026-11-12.md`、11-12 夜）

| 番号 | 内容（事実の節） | 扱い |
| --- | --- | --- |
| BR34 | 古い docstring・見出し 6 件（§1：DeltaLocalization:19、FreeDeltaFrobeniusFlat:29、AndreFlatness:19、Surjectivity の節、PerfectoidAlmost、Derived/Interface の旧見出し） | B3（BR25 と同じ docstring の回） |
| BR35 | `exists_monicRootPerfectoidExtension` の二重証明（Variants/Auxiliary:1541 と Transfinite/Tower:1172） | 保守（BR10・BR13 と一緒に） |
| BR36 | `exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed` が三つ（Transfinite の step 仮定版、Andre の仮定なし版、Inputs の版） | 保守（Inputs の版は A9 で E3 を置き換えるときに整理） |
| BR37 | `freeDeltaFrobenius_isCompletelyFaithfullyFlat`（外から未使用）と `crystallineCompletelyFlat_frobenius`（より一般） | 保守（前者を後者から出すか削除） |
| BR38 | Lemma 2.38 の r=1 の旧版（`PrincipalDP*` 1,547 行、`Andre/Envelope/PDivision` の二つ）が一般版と並ぶ | 保守（BR6 に含める） |
| BR39 | 同じ名前の宣言：`exists_perfectoidization_of_finite`（Inputs と Derived/IntegralExistence）、同じファイルの `exists_perfectoidization_of_integral`（:422・:467）・`perfectoidization_excision_isPullback`（:499・:555）、`isCoproduct`（PrismaticFrameCoproduct と CechAlexanderCoproduct）、`baseExtension`（ArcPerfectoidBase と DifferentialGraded/Resolution） | 保守（名前を分ける）。Inputs の版は A9 で |
| BR40 | 有限完全 Tor 振幅の定義が三つ（drafts の A1・A0 の二つと本体の `HasCochainCompleteTorAmplitude`）、drafts の `bockstein_sq_zero'`・`cechIndex` が本体と重複、drafts の `Construction61Hypotheses`（D77 のとおり） | 計画：⑤∞ が drafts を本体へ移すとき、本体の宣言に置き換える（5∞-2・5∞-3） |
| BR41 | BS の内側の層の逆向き：`Delta/DividedPower/FrobeniusDivisionPD` が `Prismatic.CrystallineTensorRegularity`・`Andre.Envelope.PDivision` を、`FrobeniusDivisionRegularSequence` が `Andre.PowerRootEnvelope.Completion` を import（§2 が §3〜§7 に依存） | B3（BS の整理の静的検査で、使う補題を Delta 側へ移すか、importer を移す） |
| BR42 | 名前の紛らわしさ：ファイル `Semiperfectoid/QuotientPerfectoidization` と定義 `QuotientPerfectoidization` の所在の不一致 | B3（ファイル名を中身に合わせる） |
| BR43 | 名前の紛らわしさ：`perfectoidIdeal` と `perfectoidKernel`（定理名は `perfectoidIdeal_radical`）、`IsAlmostZero` と `IsJAlmostZero`、`perfectoidBaseRing` の docstring の「R₀」 | 保守（docstring の訂正は B3 の docstring の回でよい） |
| BR44 | `idealTensorEquiv`・`idealBaseChangeEquiv`（Prism/Basic/Rigidity）が外から未使用 | 保守（BR8 の調査に含める） |
| — | S′ の有限段の 3 ファイルが Prismatic/ にある | B3 で `Semiperfectoid/FiniteEnvelopes/` へ（段 0 の案のとおり） |
| — | 地図とノートの食い違い：**Not 7.1** は地図が正しい（qrsp の定義 `IsQuasiregularSemiperfectoid` は drafts にしかない）。**Lemma 4.8** も地図が正しい（`Prism/PerfectPrismHomLift` にあり、W17 の H5 が有界な標的への一意な持ち上げとして使う。主経路の上）。 | 閉（ノートの側の記述が古い） |
| — | 原典との差で D 番号のないもの（Ex 2.21 の係数環が ℤ の局所化、Rem 2.37 は通常の Tor、Lemma 3.7 (2) は通常の導来圏、Cor 3.12 の層条件は環値前層と Čech の完全性、Lemma 2.36 (a) は p 完全平坦性から） | 記録のみ（いずれも「定理は特別な場合だけ」の範囲。D 番号は付けない） |

## 7. 原典の節ごとの見直し（ノートのチャット、11-12 から）

ノートのチャットが原典の §2 から順に、節ごとに提案を `research/bs-section-review/` に置く。**A（リファクタ）**はこの台帳の番号で扱いを決める。**B（新しく形式化する項目）**は、E3 の経路に要らないものを「補完」として §8 に並べ、空いたレーンの仕事にする（E3 の sorry 0 を先にする）。

**方針（11-12、ユーザー）**：Lean の docstring は原典の番号で引き、ノートへの参照（ノートの番号、T・BR・R のラベル）を置かない（README の Conventions）。今ある 22 か所（`research/bs-section-review/lean-docstrings-citing-notes.md`）は B3 の docstring の回で原典の番号に置き換える。

### §2 δ 環（`research/bs-section-review/02-delta.md`）

| 提案 | 台帳 | 扱い |
| --- | --- | --- |
| R2-1 Delta の層の向き（三つの importer と移し先の案） | BR41 | B3（提案の表の移し先のとおり。`RegularSequencePDUniversalTor` → ScalarTensorView は §4.2 の片付けで同時に） |
| R2-2 Lemma 2.32 の節を Basic へ、Frobenius が δ 射の三つの版を一本に | BR5 | 保守（優先。R2-3・R2-4 の前提の循環を切る。ファイルの移動だけなら B3 で、証明の置き換えは保守） |
| R2-3 Lemma 2.38 の r=1 の旧版を一般版に、階乗部分環への同型 6 つ、`RankOneDP` の並行 | BR6・BR38 | 保守（優先。R2-1 の後） |
| R2-4 自由 δ 環の Frobenius の平坦性 4 か所を一本に | BR37 | 保守 |
| R2-5 ℤ の δ 構造（`private integerDelta`）を公開し、ℤ 版の自由 δ 環を相対版の abbrev に | BR4 | 保守（B の Ex 2.6 と一緒に） |
| R2-6 δ 環のテンソル積：一般形 `tensorDeltaStructure` は 11-10 からある。完全 δ 環の版は二重 | T2-0 → 閉、新 BR45 | T2-0 は閉。BR45（`perfectDeltaTensorStructure` を一般形の系に、未参照 6 宣言）は保守 |
| R2-7 置き場所：分冪代数（FreeDP*・TruncatedPolynomialBasis・RankOneDP）を `CommutativeAlgebra/DividedPowers/` へ、Def 2.42 の `IsCompletelyRegularRel` を Delta へ | BR32 | B3（B3 の配置案に足す。RegularSequencePD* は Delta に残す） |
| R2-8 使われていない宣言・ファイル（監査だけが参照する葉 219、未参照 9） | BR8 | 保守（E3 の経路で A0〜A2 が Lemma 2.36〜2.39 を使うかを ⑤∞ で見てから） |
| R2-9 docstring（BR34 の 2 件、台帳にない 10 件ほど、統合前の名残の見出し 228 か所、ノートの番号の引用 7 ファイル） | BR34・BR25 | B3（docstring の回） |
| R2-10 小さな一般化（`isDistinguished_iff_of_span_eq` など） | 新 BR46 | 保守 |

## 8. 補完（E3 の経路の外で、原典にあって本体にないもの）

E3 の sorry 0 には要らない。レーンが待ちで空いたときの仕事として、小さいものから。順は ノートのチャットの「推奨」と規模で決める。

| 節 | 項目 | 規模 | 時期 |
| --- | --- | --- | --- |
| §2 | Ex 2.6 の残り（δ が p 進付値を 1 下げる、δⁿ(pⁿ) は単元）と ℤ の始性の公開 | 小 | R2-5 と一緒（保守） |
| §2 | Rem 2.27 の右随伴 lim_φ | 小（300〜600 行） | 空いたとき |
| §2 | Lemma 2.33 の一般形（一般の完全 p 完備 A） | 小 | 空いたとき（Ex 2.20 (3) の ξ の前提） |
| §2 | Rem 2.40 の前半（D_I(A) は φ の引き戻し） | 小 | 空いたとき |
| §2 | Rem 2.29 の二つの例（原典の文言は「この φ を持つ δ 構造がただ一つ」と読む） | 小 | 空いたとき |
| §2 | Lemma 2.43・Cor 2.44 の離散版 | 中 | Prop 3.13 の一般形を形式化するとき（今は変数の場合で足りる） |
| §2 | 後回し：Rem 2.40 の後半・Warning 2.41、Ex 2.20 (2)〜(4)、Lemma 2.11 の残り・Cor 2.12、Rem 2.13・2.7、Cor 2.31 の圏同値、Lemma 2.18 のエタール部分、Rem 2.22 | 中〜大 | 使う場所が出たとき |
| §2 | 入れない：Rem 2.3（λ 環）、単体的な版（A2 の後）、Lemma 2.38 の無限列 | — | — |
| E∞ | **coherent な Sp 値の P⁰**（DAG XIII Constr 2.2.6 の形）。D79 の改訂（11-13）で BS の経路から外した。土台は main に置く：`EInfinity/PowerOperation/`（178 本、D79 (ii) の V_{F_p}・π/H 比較 7,194 行と (iii) の鎖模型の部品 3,022 行、5a94b4d6c）。うち May 案が直接使うのは約 300〜450 行（BS-W16 報告 §96.6） | 大（残り 12,300〜22,100 行、§94） | HA の基盤の課題と一緒に（段階 II の後） |

### §3 prism（`research/bs-section-review/03-prism.md`）

| 提案 | 台帳 | 扱い |
| --- | --- | --- |
| R3-1 `IsBoundedPrism` を `Prism/Basic` へ下ろし、Prism → Prismatic の逆向きの import を消す | 新 BR47 | B3（移動）。`OrientedPrism.isBoundedPrism_of_perfect`（Lemma 3.8 (2)）の新しい補題と、手書きの 22 か所の置き換えは補完（§8）／保守 |
| R3-2 §3 の本体が §7（Andre・Semiperfectoid）の一般の補題に依存（5 importer） | BR41 に追加 | B3（提案の表の移し先。完全平坦性の閉包性質は `CommutativeAlgebra/CompletelyFlat/` へ、Pair の正則性は `HomologicalAlgebra/DerivedCompletion/Pair/` へ） |
| R3-3 置き場所（PDCompletionPrism → §7 と一緒に、`Prism/Residue/PrismaticResidue` → HomologicalAlgebra、`PerfectDeltaResidue` → `Andre/Perfection/`、`Prism/Tensor/` → Perfectoidization、Thm 3.10 の芯 4 本 → `Prism/Perfectoid/`） | BR19 ほか | B3 |
| R3-4 名前空間をそろえる（`Prism/Bounded/Completeness`・`Tilt`・`PerfectPrismHomLift` が `…Andre`） | 新 BR48 | B3（同じ回の改名表に入れられれば。無理なら保守） |
| R3-5 二重の構成（Lemma 4.8 の二版、零環の prism 二つ、Lemma 3.5 後半の手組み 5 か所、A_inf の模型二つ） | BR13 ほか | 保守。(e) drafts と本体の重なりは §4 の R4-1 へ |
| R3-6 docstring（ノートを引く 5 か所、古い記述、工程ラベル 67 行） | BR25・BR34 | B3（docstring の回） |
| R3-7 使われていない宣言 | BR8 | 閉（原典の項目にあたる宣言は、利用者がなくても残す） |

### §4 site（`research/bs-section-review/04-site.md`）

| 提案 | 台帳 | 扱い |
| --- | --- | --- |
| R4-1 drafts の A0・A1 の古典的な部分は本体に置き換わっている（約半分、表のとおり） | BR40 に追加 | **5∞-0**（⑤∞ の最初の段）：drafts を本体の宣言を指す形に書き換え、重なる宣言を drafts から外す。⑤∞ が古い drafts の上に積まないように |
| R4-2 本体の `flatTopology` は原典どおり（Cor 3.12 で site を示してから位相）。D22 を直す | — | 閉（調整役が a0-design D22 に注記した） |
| R4-3 設計書・地図の古い記述（design-status の A0-3b・A0-3d・A0-4、a0-design §1・§2.6、a1-design の Lemma 4.10、`PrismOver.lean:59` の docstring） | — | design-status と a1-design は調整役が直した。`PrismOver.lean:59` は B3 の docstring の回 |
| R4-4 Lemma 4.8 のファイルの名前空間・見出し・置き場所（`Prism/Perfectoid/` へ） | BR48 | B3。有界性の仮定の書き方は BR47 の後に保守 |
| R4-5 二重の構成（`hodgeTate_iso_polynomial_Zp` の別名、Čech–Alexander の三つの模型、`isCoproduct` の同名、Tor 振幅の定義三つ） | BR39・BR40 | 保守（三つの模型は原典の三つの構成に当たるので残す）。Tor 振幅は 5∞-0 で本体の `HasCochainCompleteTorAmplitude` に寄せる |
| R4-6 置き場所（Construction61Detection・Reflection → §6、Cor 5.5 を §5 へ） | — | B3 |
| R4-7 docstring | BR25 | B3 |

### 補完への追加（§3・§4）

| 節 | 項目 | 規模 | 時期 |
| --- | --- | --- | --- |
| §3 | Def 3.2 の prism の圏（`Category` の instance）、Def 3.2 (3) の平坦な射（`OrientedPrism.Hom.IsFlat`・`IsFaithfullyFlat`、site の定義をその略記に） | 小 | **5∞-0**（Thm 3.10 の圏同値と Rem 4.6 の前提） |
| §3 | Lemma 3.8 (1)(2) の名前つきの補題（`isBoundedPrism_of_perfect` など）、Lemma 3.5 後半の向き付きの構成子 `OrientedPrism.ofDeltaHom`、Lemma 3.6 の向き付き版、Ex 3.3 | 小 | 5∞-0（BR47 の後） |
| §3 | **Thm 3.10 の圏同値（絶対版、向き付き）** | 小〜中 | **計画**：Rem 4.6 の同値（G-A5-4）の前提で、5∞-6（A5）の前に。部品はそろっている |
| §4 | **prismatic site の本質的小ささ**（結晶 site の `CrystallineSiteSmall` と同じ証明。本体の `[EssentiallySmall …]` の仮定を外す） | 小 | **5∞-0** |
| §4 | **Rem 4.6 の定義**（完全 prism の充満部分圏と誘導位相） | 小 | **5∞-0**（5∞-6 の A5 の前提） |
| §3・§4 | 後回し：Lemma 3.1 (3)、Lemma 3.7 (3) を圏の同一視として、Lemma 3.9 の付随の主張（BR28 の残り）、Thm 3.10 の perfectoid の定義の差、Cor 3.12 の絶対版 | 小〜中 | 使う場所が出たとき |
| §3・§4 | 入れない：Def 3.2 の一般の Cartier 因子、Lemma 3.7 (4)、Rem 3.11、Ex 3.14 の一般形、Prop 3.13 の一般形（D21）、Def 4.1 の形式スキーム版、Rem 4.3・4.7・4.13〜4.15、Construction 4.4、Lemma 4.21、Lemma 4.8 の一般の標的、Thm 4.11 の smooth な一般の R | — | E3 に要らない、大きな基盤がない |
| §4 | 計画済み（⑤∞）：Notation 4.16、Construction 4.18「Δ を計算」と Ō 版、Rem 4.19 の Tot、Lemma 4.20・4.22（5∞-2）、Thm 4.11 の一般の基底と Cor 4.12（5∞-3） | — | — |

### §5・§6 HT 比較（`research/bs-section-review/05-hodge-tate.md`）

| 提案 | 台帳 | 扱い |
| --- | --- | --- |
| R5-1 drafts/A1 の古典部分（CrystallineInput・CrystallineSite・DeRhamComparisonPoly・HodgeTateComparison）は本体に置き換わっている | BR40 に追加（R4-1 を A1 の残り 3 本に広げる） | **5∞-0** |
| R5-2 Prop 6.2 (b) と Cor 5.5 の一般の結晶 prism（drafts の二つの sorry）を `hodgeTate_iso` の系に | — | **5∞-0**（入らなければ 5∞-3a の最初）。原典との順序の違いは docstring に一行 |
| R5-3 (a) `arcPadicIntMap` を `HomologicalAlgebra/DerivedCompletion` へ（§6 → §8 の import を消す） | 新 BR50 | B3 |
| R5-3 (b) `PDCechFrameHomotopy` の汎用の部品（`algebraModule`・`cochainHomotopy`・添字の補題）を `HomologicalAlgebra/Cosimplicial/Algebra` へ | BR50 | B3 |
| R5-3 (c) §4 の名前で中身が §6.4 の 5 本を §6.4 の側へ | — | B3 |
| R5-3 (d) 「Crystalline 204」を §0 の (a)〜(e) で分け直す（(e) は `CommutativeAlgebra/DividedPowers/`、R2-7 と同じ行き先） | — | B3 |
| R5-3 (e) 名前空間（63 本） | BR48 | B3（同じ回の改名表） |
| R5-4 (a)〜(c) 別名・包み・pd 模型の複数 | BR39 | 保守（模型は D68・D69 が使うので残す） |
| R5-4 (d) 導来 Nakayama の二つのファイル（`DerivedCompletion/CompleteCochainReduction` と `CochainCompleteDetection`） | 新 BR49 | 保守（統合） |
| R5-4 (e) Tor 振幅の名前の重なり（drafts の ∞ の型と本体の `Construction61.*`） | BR40 | 5∞-0（BR40 の一本化と一緒に） |
| R5-5 docstring の工程ラベル（49 行・22 ファイル、「第二比較」を数学の言葉に） | BR25 | B3 の docstring の回 |
| R5-6 閉包・葉・未使用の宣言 | — | 消さない（∞ の組み立ての入力として使われる予定） |
| R5-7 設計書の古い記述（second-half の 5∞-3、a1-design の Prop 6.2 の名前・G-A1-12・§2.4 の D77） | — | 閉（調整役が 11-12 夜に直した） |

計画の上の点（§3.1）：
- 5∞-3 を **5∞-3a（古典：Prop 6.2・Thm 6.3・Cor 5.5 の系、Lemma 4.22 の鎖複体版、G-A1-10）** と **5∞-3b（Cor 4.12 の CAlg 値、D27）** に分けた。5∞-3a は B3・5∞-0 の後に ③-b を待たずに始める。drafts の ∞ の型（`HasFiniteCompleteTorAmplitude`・`baseChangeB`・`affineModuleDiagram`）は古典の型に置き換えてよい。Construction 6.1 の ∞ の型への橋渡し（`moduleReflection`）は 5∞-3b で要るときだけ。
- Thm 6.4（D69）の ∞ の組み立てを **5∞-4b** として明示した（依存 5∞-2・5∞-3b・5∞-4・3b-4、5∞-6 の前）。

### 補完への追加（§5・§6）

| 節 | 項目 | 規模 | 時期 |
| --- | --- | --- | --- |
| §5 | Cor 5.5 の一般の結晶 prism（系として） | 小 | 5∞-0 か 5∞-3a（R5-2） |
| §6 | Prop 6.2（一般の有界向き付き基底、一般の r）・Thm 6.3（多項式の場合） | 中〜大 | 5∞-3a |
| §5 | 後回し：Not 5.1 の ψ と \(R^{(1)}\)、一般の Thm 5.2、Lemma 5.4 の加群版、Thm 6.4 の一般の基底（D69 の後なら安い） | 小〜中 | 使う場所が出たとき |
| §5・§6 | 入れない：Rem 5.3、Cor 5.5 の smooth な \(S\)（Lemma 4.21）、Thm 6.3 の étale 局所化 | — | — |

### §7 semiperfectoid（`research/bs-section-review/07-semiperfectoid.md`）

| 提案 | 台帳 | 扱い |
| --- | --- | --- |
| R7-1 drafts/A3 の古典部分は本体にある（約 26 の sorry）、A3 が EInfinityTheory に移っていない、A2 の `Poly` の衝突、A1 の `prismaticCohomology_lci_universal` を A3 へ | BR40 に追加 | **5∞-0** |
| R7-2 (a) 忠実平坦版と並ぶ三段の系列（非忠実平坦版を一行の系に） | 新 BR51 | 保守（優先） |
| R7-2 (b) 名前のない述語（有界 p 冪ねじれ 30 本・67 行、semiperfectoid） | — | 定義は **5∞-0**、展開形の置き換えは保守 |
| R7-2 (c) `OrientedPrism.ofDeltaHom` は `ofDiscreteDelta` としてある | §8 の §3 の行 | §3 の補完の行を「`ofDiscreteDelta` の向きを確かめる」に読み替える |
| R7-2 (d) A_inf の模型三つ | R3-5 | 残す |
| R7-3 (a) KST → BS（`MonicRelation` を `CommutativeAlgebra/KoszulRegular` へ） | BR26′ に追加 | B3′ |
| R7-3 (b)〜(d) §7.2 → André の内部（8 辺）、`PowerRootPolynomial`、`exists_boundedPerfectPrismPresentation` の置き場所 | BR41 に追加 | B3′ |
| R7-4 配置案を項目ごとに（`Cotangent/` は空、Discrete・Lci・Quasiregular・Perfection・Surjectivity） | — | B3′ |
| R7-5 名前空間 | BR48 | B3′ |
| R7-6 (a)(b)(d) 閉包・葉・未使用 | — | 消さない |
| R7-6 (c) root から届かない 9 本（RootEnvelope 3、PerfectPrismDivisionComparison、PDivisionSource、Audit 4） | BR8・BR14 | B3′ で判断（Audit 4 本は BR14 で scripts/ へ。残りは root に足すか archive か） |
| R7-7 docstring（「（旧 パス）」571 か所ほか）、存在しないパス 9 件、`@[cite]` の注意（Rem 7.15 は `partial` か Thm 7.14 の証明として、Prop 7.11 は付けない） | BR25・BR34 | B3（引用の注意は今夜の B3 の属性付けに入れる）、残りは B3′ |
| R7-8 設計書の古い記述（a3・a2・design-status・地図 7.1 の goal） | — | 調整役が直す（11-13）。7.1 の goal は地図の判断として保留 |

### §8 perfection（`research/bs-section-review/08-perfection.md`）

| 提案 | 台帳 | 扱い |
| --- | --- | --- |
| R8-1 E3 界面が三つの型（CAlg_R 版 3 本は使う側 0）、EInfinity → BS の逆向き 2 本 | BR26′ に追加、新 BR52 | B3′：TheoryInterface を BS へ移す。CAlg_R 版 3 本の削除は保守（BR8 の方針：削除は保守） |
| R8-2 Derived/Interface の環の部分を切り出す（環の 7 本と §6 の 1 本の閉包から ∞ が消える） | BR50 と同じ回 | B3′（効果が大きいので B3′ の最初） |
| R8-3 IntegralExistence を三つに分けてから動かす | — | B3′（今夜の B3 の案で丸ごと移すなら、移さずに残す） |
| R8-4 同じ名前の宣言 | BR39 | `SerrePositivity/Inputs/Perfectoidization.lean` の削除は B3′、`BhattScholze.Inputs` の整理は 5∞-9（A9） |
| R8-5 `comp_ringEquiv`／`precomp_ringEquiv` | BR21 に追加 | 保守（優先） |
| R8-6 底変換の四つの構成、Witt の余積の模型（約 560 行を外せる見込み） | BR22 に追加 | 保守 |
| R8-7 TensorCompatibility の公開、BR31 を狭める | BR23・BR31 | BR23 は B3′、BR31 は「導来版と Cor 8.14 から同じ主張が出ることを確かめる」に狭める |
| R8-8 `Derived/` → `Interface/`、drafts の行き先の欄、Applications、FiniteProduct | BR48 | B3′ |
| R8-9 docstring（工程ラベル 65 行、「（旧）」44 行、古い記述） | BR25・BR34 | B3′ の docstring の回 |
| R8-10 drafts と本体の重なり・同名・古い記述 | BR40 に追加 | **5∞-0** |
| R8-11 設計書の古い記述（a4・a6・a7・a9・design-status） | — | 調整役が直す（11-13） |
| R8-12 閉包・葉・未使用 | — | 消さない（CAlg_R 版 3 本と R8-4 の 2 宣言は保守で削除） |
| R8-13 原典の形との違い | — | 記録だけ（Inputs の docstring にある） |

### §10 almost（`research/bs-section-review/10-almost.md`）

| 提案 | 台帳 | 扱い |
| --- | --- | --- |
| R10-1 単項の `perfectoidIdeal` と一般の J の `perfectoidKernel` の二系統、一般形が CompletedTensor にある | 新 BR53 | 結ぶ補題と一般の J の系は **5∞-8c**。単項の側の重ねた証明（conormal 経由の冪等性約 240 行など）の整理は保守（優先） |
| R10-2 BR24 の範囲（85 か所・12 ファイル、参照先が古い） | BR24 | 保守のまま、範囲を書き直した（この表を正とする） |
| R10-3 名前の紛らわしさ | BR43 | B3′ の改名表 |
| R10-4 drafts/A8 と本体の同名 40 | BR40 に追加 | **5∞-0** |
| R10-5 (a) SupportedQuotient を ExcisionTor の隣へ | — | B3′ |
| R10-5 (b) `mul_eq_zero_of_pow_mul_eq_zero_of_reduced` を CommutativeAlgebra へ | BR41 に追加 | B3′ |
| R10-5 (c) `IsConnectiveAt`・`isPCompleteVertex`・CompletedModuleTensor を一般の場所へ | — | **5∞-0**（drafts と衝突する前に） |
| R10-5 (d) §10 の芯が `Perfectoidization/CompletedTensor` にある | — | B3′ |
| R10-5 (e) Lemma 10.12 の 36 本が root の外 | — | **閉**（11-13、調整役が root に足した） |
| R10-5 (f)(g) 名前空間、B3 の配置案への意見 | BR48 | B3′ |
| R10-6 閉包・葉・未使用 | — | 消さない |
| R10-7 docstring（Lemma103:20 のノート参照を含む） | BR25・BR34 | B3（ノート参照は既存の 22 か所と同じ回）、残りは B3′ |
| R10-8 設計書・地図の古い記述 | — | 調整役が直す（11-13）。second-half の 5∞-8 は直した |

**B3′**（11-13 決定、**11-15 に実施・取り込み**：`bulk-b3prime.md`、22 項目。取り下げは DivisionResidue 全体の移動（独立した 12 宣言だけ抽出）。以下の表の「B3′」は実施済み）：§7・§8・§10 の見直しで B3 に当たる移動・改名は、今夜の B3（B2 で固めた範囲）に入れず、二度目の一括の回 B3′ にまとめる。B2 の停止点の当日に範囲を広げると、B2 のやり直しになるため。B3′ は B4 の後、⑤∞ の段が新しいファイルを置き始める前を目安にする。

### 補完への追加（§7・§8・§10）

| 節 | 項目 | 規模 | 時期 |
| --- | --- | --- | --- |
| §7 | Prop 7.10 (ii) S′ の単位の p 完全忠実平坦性（W17 §16 の 3 点） | 700〜1,000 行 | 空いたとき（古典、∞ に依らない） |
| §7 | 後回し：Prop 7.10 (iii)(iv) の一般の qrsp、Rem 7.15 の主張 | 中〜大 | 使う場所が出たとき |
| §8 | 後回し：Ex 8.3 | 小 | 5∞-6 の後 |
| §10 | Def 10.1 の J=(p) での等号、Rem 10.7 の冪等と ∀ g の系 | 小 | 5∞-8c と一緒に |
| §10 | 後回し：Prop 10.2 の (R/J)_perfd 加群の圏との同値（D14・D66 を加群の段階でも保つか要確認）、Prop 10.4 の厚いイデアル、Rem 10.7 の平坦性、Thm 10.9 (c) | 小〜中 | 使う場所が出たとき |
| §7・§8・§10 | 入れない：Prop 7.2・Cor 7.3 の Δ^init の部分（D37）、Prop 7.11・Ex 7.12・7.13（D38）、Def 8.7・Lemma 8.8 の一般形、Rem 8.9、Cor 8.11（D55）、Def 10.6・Prop 10.8・Thm 10.9 (d)(e)（D63）、Prop 10.4 の同値（D66）、Rem 10.10・10.13 | — | — |

## 9. 追記（2026-11-12 夜）：D79 で界面が KST を import した

D79 (i)（615ceab26）で、E∞ の界面 `EInfinity/Interface/Theory.lean` が `KST.LocalizingInvariants.SpectrumHomotopyFunctor`（Ω スペクトルの準圏 `KST.Spectra.Sp` と `SpectrumHo.piFunctor`）を import するようになった。BS の主定理の閉包に KST のディレクトリが入る。中身は ∞ の一般論（R83 と同じ問題）なので、**R83 の一部として、`KST/Spectra` の Sp と `SpectrumHo` を InfinityCategories（Kerodon か HA の安定 ∞ 圏の節）へ移す**。KL-W1 の改名表は KST/Spectra を含まないので、新しい改名表を作る。時期：B3 に入れられれば B3、無理なら保守の先頭（BS の閉包を直すので優先）。

## 10. 追記（2026-11-16）：略号表が import の連鎖にある（BR54）

| 番号 | 問題 | 扱い |
| --- | --- | --- |
| BR54 | `Util/Citation.lean` の略号表（`knownKeys`・`knownEditions`、`bibliography.json` から生成）が属性の定義元と同じモジュールにあり、直接 896 本が import する。略号を一つ足すだけで root がほぼ全部再ビルドになる（11-16、65 分以上、四レーンが約 1 時間止まった） | 計画：属性の定義元からキーの検査を外す。属性はキーを記録するだけにし、検査は import の連鎖に入らない検査スクリプト（`bulk_citation_registry.py --check` と同じく `bibliography.json` と環境の記録を突き合わせる）か、照会コマンド `#cite_tags` と一緒に変更の少ない別モジュールへ。夜の一括で。それまで略号の追加は夜にまとめる（`coordination.md` §2） |

## 11. 追記（2026-11-17）：弱い存在命題からの choose（BR55）

| 番号 | 問題 | 扱い |
| --- | --- | --- |
| BR55 | 既存の定義が、弱い存在命題（「指定頂点を持つ極限錐がある」「底の等式と前合成同値性を満たす比較がある」など）から `Classical.choose` でデータを選び、指定構成（余単位・span・相対同型など）との両立を失う。5∞-1 で三回、既存の本文を直した（S8 の錐の選び方、`smallLeftUnstraighteningComparisonOfFunctorIso`、`leftCoherentTransportDirectComparison`）。InfinityCategories には `Classical.choose` を含むファイルが多数ある | 計画：③-a の 255 本（5∞-1 の範囲、N1〜N5 は適用済み）と ⑦ の追加 362 件（要らない 6・不明 356、`research/infinity-consolidation-w1/choose-additional.md`）。**不明は使う段で直す**（ユーザー 11-17）。洗い出しは **⑦ IC-W1 の IC-1 段 0** に含めた（ユーザー決定 11-17 案 A、`stage-ii/consolidation/infinity-consolidation-w1.md` §7）。5∞-1 の依存分は ③-a の紙（11-17）。「要る」と判定したものは IC-W1 の移動と同じ夜にまとめて直す。事前承認の型は `inf-supply-w1.md` 11-17 朝の追記 |

## 12. 追記（2026-11-17）：Archive の扱い（BR56）

| 番号 | 問題 | 扱い |
| --- | --- | --- |
| BR56 | `SerrePositivity/Archive/`（1,871 本・約 11 万行）はビルドしないので検証されず、改名・移動の道具が毎回書き換えている。対応表の行が Archive の宣言を own と記録していた（Kerodon 9.1.1.20） | ⑧ AR-W1（`research/archive-review/`）で数学の中身を確認し、ユーザー決定（11-17）：**戻す 5 本**は P⁰ の段 0 で本体へ（`p0/p0-plan-draft.md` §9）。**材料 161 本**（FilteredExchange の引き戻しの 94 本は Kerodon 9.1.5.7 の後、KST/DescentConditional の 67 本は K の再開時に判断）。**消してよい 69 本**（dg の U12e の検査 68 本、WIP の RelativeFiller 1 本）は 11-17 に消した（タグ `archive/archive-u12e-relativefiller-2026-11-17`）。**判断できない 1,636 本**は凍結し、Kerodon 9.1 の項目を本体で形式化した後に判断。それまで改名・移動の道具と集計の対象から Archive を外す（IC-W1 §10）。9.1.1.20 の own は partial に直した |

