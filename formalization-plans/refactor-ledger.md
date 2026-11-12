# リファクタ候補の台帳

作成：2026-11-12（段階 II の調整役）。決定：ユーザー（11-12、リファクタ候補はノートではなく形式化の側で管理し、扱いは調整役が判断する）。

この台帳が**リファクタ候補の状態の正本**。勉強ノート（`exposition/ja/bs/` の BR、`exposition/ja/infinity/` の R）には今後リファクタ候補を書かない。ノートを書いていてコードの問題に気づいたら、事実を `research/` にまとめ、ユーザーから調整役へ伝える。

- 取り込み元：`research/bs-refactor-audit/`（BR1〜BR33、ba24dceb6）、`research/infinity-refactor-audit/`（R 番号、同）。囲みの原文はそれぞれの `box-texts.md`。ノートにしかなかった調査（R8 の重複、R58 の Yoneda の閉包）は `research/infinity-refactor-audit/r8-duplication.html`・`route-yoneda.html` に写した。
- ∞ の R 番号の**中身**の正本は従来どおり `refactoring-infinity.md` §0 の索引から辿れる文書（R1〜R79）。ただし §0 の状態欄とパスは 10-30 のままで古い。**状態はこの台帳を正とする**。
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

中身の正本は `refactoring-infinity.md` §0 の索引。ここには状態と扱いだけを書く。§0 の「中身が正本と同じ」R（監査 README §1 の列挙）は、下の表に挙げないものは §0 の状態のまま。

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
