# BS 勉強ノートのリファクタ候補 BR1〜BR33 の現状（2026-11-12）

作成：BS の地図とノートのチャット（形式化の調整役ではない）。基準：main ba24dceb6。読み取りだけのエージェント 3 本で調べ、主な主張（逆転の 2 件、refactor-plan の記述、BR28 の定理）は作成者が grep で確かめた。

- 目的：形式化の調整役への受け渡し。ユーザーの方針（11-12）で、リファクタ候補はノートでなく形式化の側で管理し、扱い（実施・計画への取り込み・不要）は調整役が判断する。**ここには事実だけを書き、推奨や振り分けは書かない。**
- ノートの側の予定：調整役が台帳に取り込んだ後、`exposition/ja/bs/` の赤い囲み（33 個）と index.html の「リファクタ記録」の表を外し、台帳への参照に置き換える。囲みの原文は `box-texts.md` に写してある（ファイル:行は ba24dceb6 時点）。
- 経緯：BR は 10-25〜11-02 にノートを書きながら付けた。その後の BS-W1〜W17 は BR 番号を挙げずに内容を片づけたことが多く、index の状態欄は 33 件中 27 件が実態と食い違っていた（一致は BR1・2・3・9・30・31）。
- 「状態」の語：**実施済み**／**一部実施**（済んだ部分と残りを書く）／**未実施**／**前提が変わった**（ノートの提案の前提が後の決定や変更で成り立たない）。「計画書」は refactor-plan.md、cleanup-list-2026-11.md、stage-ii/citation-attributes.md（B3）、stage-ii/stage-ii-second-half.md、bhatt-scholze/design-status.md、bhatt-scholze/bhatt-scholze-stage2.md、a*-design.md を内容で探した結果。B3 の配置案は `refactor/kerodon-layout` 枝の `formalization-plans/stage-ii/bulk-w1-b2/layout/module-paths.csv`（400624b0d）を見た。

## 1. 一覧

| BR | 提案（一行） | 状態 | 根拠 | 計画書での扱い |
| --- | --- | --- | --- | --- |
| BR1 | 直下の平置きを主題別のディレクトリへ | 実施済み | 2d288b899、W2〜W4 の moves.json。直下の .lean は 0 本 | — |
| BR2 | 普遍性の手書き展開 3 か所を `IsPerfectoidization.precomp_ringEquiv` へ | 実施済み | e039377a6。今は `Semiperfectoid/Surjectivity.lean:271`・`:301`、`RootEnvelope/Source.lean:1852` | — |
| BR3 | 監査 838 行の環 instance の不一致 | 実施済み | 9095aff46（`scripts/audit_bhatt_scholze_refactoring.lean:802` に `(R := L)`） | — |
| BR4 | 自由 δ 環の ℤ 版と相対版を一本に | 未実施 | `Delta/Free/FreeDeltaRing.lean` に独自の構成・普遍性（:160・:190）と比較（:238）。W5（62decba97）はファイル統合のみ | なし |
| BR5 | p 正則版 `isDeltaHom_frobeniusLift` を一般版で置き換える | 未実施 | p 正則版 `Delta/Perfect/PerfectDelta.lean:288`、一般版 `Delta/Free/FreeDeltaRing.lean:276` が並ぶ | なし（index は「W2 の候補」） |
| BR6 | pd 包の同型の三角形・分冪構造の三重構成を一本に（T2-1・T2-2 と同時に） | 未実施（重複は増えた） | T2-1 は W15 K1（31feb833a ほか）で一変数版と独立に実施。`PrincipalDP` は `RegularSequencePD` を import しない。階乗部分環との同型は `principalDPFactorialEquiv`・`dpFamilyFactorialEquiv`・`freeDPFactorialEquiv`・`frobeniusDivisionFactorialEquiv`・`pDivisionFactorialBaseEquivOfDividedPowers` | なし |
| BR7 | 根の関係とモニック関係の並行ファイル群 | 未実施 | `Andre/Envelope/RootFamilyRaw.lean` と `Andre/Variants/RootedExtension.lean`（:956 ほか）。07 章 151 行に評価はあるが決定なし | なし |
| BR8 | どこからも使われないモジュール 173 本の扱い | 一部実施 | W8 で Supplement 31 本を削除（5a6e3285a）、W5〜W8 の統合で大半は他のファイルへ。今、集約からしか（または全く）import されないものは 60 本（9＋51、うち 53 本は監査が import）。大半は段階 II の新しいもの（Prismatic 28、Perfectoidization/Derived 8）。宣言単位の確認はしていない | なし（refactor-plan は BS を対象外、B3 の片付けは KST と Diagnostics） |
| BR9 | Thm 7.4 を Thm 7.14 の系に、旧証明は別名で残す | 実施済み | f4dcf1d1a・7b82e02aa。`Semiperfectoid/Surjectivity.lean:509` が `:460` を呼ぶ。旧証明は `RootEnvelope/PerfectPrism.lean:993`（root から届かない） | — |
| BR10 | André の任意族版（Variants）の重複を削除 | 一部実施／削除は前提が変わった | W8 で 4 本に統合。W8 指示書冒頭のユーザー決定「(3) Variants は残してまとめる」（10-26）。同じ型の定理が `Variants/Auxiliary.lean:1541` と `Transfinite/Tower.lean:1172`、`Variants/RootedExtension.lean:1584` と Tower:1463 に並ぶ | なし |
| BR11 | 届かない照合と旧経路（Rem 7.15 の 28 本、MonicRaw 10 本）の削除 | 前提が変わった | W8 で `Andre/PowerRootEnvelope/` に改名して全部残す決定（10-26）。root の集約 `BhattScholze.lean:477-478` が読むので既定のビルドに入る（「届かない」の前提が変わった） | — |
| BR12 | 条件付き版・重複した降下系列・旧い適用形の片付け | 一部実施 | 条件付き版は Surjectivity の André 節に（W3・W7）、`AndreCompatibleRootsConditional` は削除。重複系列は `RootEnvelope/Source.lean:1863` へ。旧い適用形 2 本（Surjectivity:553・575）は監査（audit_axioms・audit_bhatt_scholze_b4・audit_clmst_b3）だけが使う | 旧い適用形はなし |
| BR13 | 手で繰り返す証明の型（商の導来 H⁰ が 6 回、perfectoid 環の prism 表示、三段の並行）を汎用補題に | 未実施 | (a) `Andre/Envelope/RootSource:274`、`RootFamilySource:247`、`MonicCandidate:976`、`Variants/ArbitraryFamily:203`、`RootEnvelope/Source:267` ほか。(b) W17 の `exists_boundedPerfectPrismPresentation`（`Semiperfectoid/PerfectoidPrismPresentation.lean:47`）は新しいコード 4 本だけが使い、旧い 5 か所（Tower:1180、Variants/Auxiliary:1496、Variants/RootedExtension:1592、RootEnvelope/PerfectPrism:997、Semiperfectoid/Perfectoidization:388）は手で場合分け | なし |
| BR14 | ライブラリ内の監査ファイル 4 本を scripts/ へ | 未実施 | `Andre/PowerRootEnvelope/Audit/` の 4 本（`#print axioms` を含む、root から届かない） | B3 の配置案では 4 本とも retained |
| BR15 | Lemma 3.9 の p 進完備化系の層と除算の枝を消し PD 版に一本化 | 未実施 | `Prism/Perfection/PCompletedPerfection.lean` 394〜606 行（使うのは `scripts/audit_bhatt_scholze.lean` 842〜886 行だけ）。除算の枝は `Semiperfectoid/PerfectPrismDivision`（517 行）・`PerfectPrismDivisionComparison`（579 行、監査 2 本だけが import）。W7（98849e356）は移動のみ | なし |
| BR16 | Fontaine 比較の正則版の枝（約 300 行）を消し、単射性の部分を独立させる | 未実施 | `Prism/Perfectoid/WittQuotientPerfectoid.lean` 184〜310・424 行、`WittQuotientTilt.lean` 394〜477 行 | **refactor-plan.md 203〜205 行に逆向きの記述**：Fontaine 核の分離性の連鎖（10 宣言、Perfectoid/Fontaine）は BS の `wittRegularQuotientFontaineMap_surjective`・`_bijective` の仮定 `IsHausdorff (ker θ)` を満たす唯一の証明として残す（10-30 ユーザー、一度削除して戻した）。正則版を消すとこの連鎖の利用者がなくなる |
| BR17 | Lemma 3.5 まわりの並存の解消と小さな繰り返しの共通化 | 一部実施 | 並存は BR27 で解消（`_of_p_regular` 0 件）、W7 で `Prism/Basic/Rigidity.lean` に集約、`Hom.span_map_generator`（Rigidity:62）。残り：「反復除算と分離性から単射」が Rigidity:227 と WittQuotientPerfectoid:339〜372 の 2 か所、「p は単元でない」が `PerfectPrismHomLift.lean:647` の private 補題など（全数は未確認） | なし |
| BR18 | 使われない完全 prism のテンソルの枝を縮める、標数 p の特殊化 | テンソル：未実施／標数 p：前提が変わった | `Prism/Tensor/PerfectPrismResidueTensor.lean`（372 行、11 宣言とも外から参照なし）。`CharacteristicP` は BS-W11 B-3（9ffa38a4e）で `Perfectoidization/Derived/ArcValuationExtension.lean:190` が使うようになった（root から届くかは未確認） | なし |
| BR19 | 原典番号・置き場所・import の逆転・複製 docstring・小さいファイル | 一部実施（ほぼ済み） | W7 と bcc42a7b8 で番号（Lemma 3.8）・逆転・複製・統合は解消。`Prism/Residue/PrismaticResidue.lean`（原典に項目のない道具）が Prism の下に残る | B3 の配置案の Prism の欄は「Basic・Perfectoid 等を保持」で、Residue は含まれない |
| BR20 | 有限直積の perfectoid 性を E3 なしで直接証明 | 実施済み | BS-W10 作業 A（fae7c9ca3、cc67ea88e）。`Perfectoid/FiniteProduct.lean:250` は `:230` からの帰納法、推移的 import に Inputs なし | — |
| BR21 | `IsPerfectoidization` に `hom_ext`・移送補題を足し、手書き展開と逐語の複製を置き換え | 未実施 | `CommutativeAlgebra/Perfectoid/Defs.lean` に `hom_ext` なし。手書き展開は `TensorPerfectoidization:407`、`CompletedTensor:539`、`TensorCompatibility:101`。複製（約 30 行）は `CompletedTensor.lean` :362 と :475。専用の `completedTensorPerfectoid_hom_ext`（:504）はある | なし |
| BR22 | 底変換と三角図式の共通化、テンソルの二つのモデル（Witt 余積と完備テンソル H⁰）の一本化の調査 | 未実施（調査も未着手） | `TensorPerfectoidization.lean:376` と `TensorCompatibility.lean:26`・`:358` が別々。Witt モデル `WittPushout.lean`（526 行）は Surjectivity・`Andre/OrdinaryRoots/Adjoin`・`RootEnvelope/Source` が使う | B3 で retained |
| BR23 | Prop 8.13 環版の公開、`isIntegralPerfectoid_of_ringEquiv` の移動、alias の削除 | 一部実施 | 4 本は `Perfectoidization/TensorCompatibility.lean` に統合、root から届かず監査 2 本だけが読む。`isIntegralPerfectoid_of_ringEquiv` は `Prism/Perfectoid/PerfectPrismPerfectoid.lean:167` のまま（21 ファイルが使用）。`PerfectCoefficientTensor` の本体は `CommutativeAlgebra/PerfectRing.lean:75` へ、互換 alias が `WittPushout.lean:27-45` に残る | なし |
| BR24 | Almost/ の supported quotient を `IsAlmostZero`・`IsAlmostIso` の言葉で述べ直す、docstring、集約 | 一部実施 | docstring は直った（`Lemma103.lean:307`）、`PerfectoidAlmost` は 534 行の本体になった。`Almost/SupportedQuotient.lean` は `IsAlmost*` を使わず手書きのまま | B3 で Almost/ は retained |
| BR25 | docstring の工程ラベルを数学の言葉に、書式を揃える | 一部実施 | 書式は 604 本中 590 本に「## 概要」（欠けるのは Prismatic 4、Perfectoidization/Derived 8、Andre/PowerRootEnvelope/Audit 2）。ラベルは 33 ファイルに残る：G 系 42 行（例 `Semiperfectoid/RootEnvelope/PerfectPrism.lean:119`）、B4-x 41 行（例 `Delta/Division/Residue.lean:161`）、A1-b 39 行、F4〜F7・N3 11 行。DOC1（bcc42a7b8）は原典番号の追加のみ | なし |
| BR26 | 共通基盤 4 本が BS を import する層の逆転 | 実施済み（元の 4 本）。**新しい逆転が 2 件** | 2a（f5ac10ee1・4934d077b、refactor-plan.md 308〜311 行）。新しい逆転（作成者が確認）：`CommutativeAlgebra/KoszulRegular/Powers.lean` → `BhattScholze.Andre.OrdinaryRoots.MonicRelation`（3139c7f27、W15）、`HomologicalAlgebra/DerivedCompletion/PrincipalCompletionUniformBound.lean` → `BhattScholze.Andre.Transfinite.Colimit`（218f8939f、W17） | 新しい 2 件はなし |
| BR27 | 剛性と distinguished 性の p 正則の仮定を外す | 実施済み | ebe9f891c（10-26、22 宣言）。`isDistinguished_generator`（OrientedPrism.lean:176）。bhatt-scholze.md 215 行に記録 | — |
| BR28 | Lemma 3.9 を原典の形（prism の完全化の普遍性）で述べ、環の普遍性を Prism/ へ | 実施済み | 移動は W7（`Prism/Perfection/PrismPerfection`）。定理は W17 停止点 5（ce4bba8f6）の `Prism/Perfection/ClassicalPrismPerfection.lean`（`existsUnique_classicalPrismPerfectionHom`:75 ほか、`Semiperfectoid/InitialPrismPerfection.lean:53` が使用）。原典の付随の主張が全部入っているかは未確認 | a3-design G-A3-8 |
| BR29 | Thm 3.10 を一つの定理に（入口、W(T♭) との比較、圏同値は後で） | 一部実施 | W(R♭) との比較は W17 H5（2eca57754）の `Semiperfectoid/PerfectoidWittEquiv.lean:72`、`AinfClassical.lean:105` ほか（置き場所は Semiperfectoid）。一つの入口はない | 圏同値は a5-design 213 行 G-A5-4、drafts `A5/PerfectSite.lean:267`（sorry） |
| BR30 | Thm 7.14 の一段の拡大を原典（Prop 7.11(2)）に揃えるか | 閉じた | a3-design D38（11-02、揃えない）、design-status 226 行 | — |
| BR31 | Prop 8.13 環版を A7 の導来版の系に置き換える | 未実施（計画にある） | 導来版は drafts `A7/AnimatedPerfectoidization.lean` のみ | a7-design §1 36・100・123・132 行、design-status 232 行。A7 は stage-ii-second-half の 5∞-8 |
| BR32 | `Delta/DividedPower/` の 74 本を原典の項目ごとに分け、(3) 生の包を Division/Prism の近くへ、(5) 分冪代数を CommutativeAlgebra へ | 一部実施 | 1e070183d（w9-merges.json）で 5 本（Factorial・PDivision・PDivisionCompletion・PrincipalDP・RankOneDP）に統合。サブディレクトリ化と (3)(5) の移動はなし。W15 で 18 本が加わり今 23 本 | B3 の配置案は「Delta は今の下位分類を保持」。design-status 41 行の `RegularSequencePDUniversalTor` の移動は KST への import を避けるための別件 |
| BR33 | §3 の内容を Prism の下へ集め、§7・§8 の内容を外へ | 実施済み | 98849e356（10-25、W7）。`Prism/Bounded/`・`Prism/PerfectPrismHomLift.lean`・`Semiperfectoid/{PerfectPrismDivision*, CharacteristicP, Perfectoidization}`・`Delta/Perfect/PerfectDeltaTensor.lean` | B3 で Prism の大分類は維持 |

## 2. 調整役の判断を待つ論点（事実だけ）

1. **BR16 と refactor-plan.md 203〜205 行**：ノートの提案（正則版を消す）と、既存の決定（Fontaine 核の連鎖を正則版の仮定のために残す）が逆向き。
2. **BR26 の新しい逆転 2 件**（§1 の BR26 の行）。どの計画書にもない。
3. **未実施で計画書に内容が見当たらないもの**：BR4、BR5、BR6、BR7、BR13、BR14、BR15、BR16、BR18（テンソル）、BR21、BR22。一部実施の残り（BR8・12・17・19・23・24・25・32）も、BR19 の Residue の配置を含めて計画書には見当たらない。
4. **11-12 の B3 の配置案で「そのまま」とされたファイルに BR の対象が含まれる**：BR14（Audit/ の 4 本）、BR19（Prism/Residue）、BR22・BR24 の対象、BR32（Delta）。

## 3. 形式化の側の文書で、調査中に古いと分かった記述

- `formalization-plans/bhatt-scholze/bhatt-scholze-stage2.md` 63〜64 行：有限直積の perfectoid 性を「E3 に依存する」と書いている。BR20（BS-W10 作業 A）で解消済み。

（ノートの側の古い記述、03 章の命題 3.7 の Lean 欄・D7 行・章末のまとめ「原典の形の定理はない」、BR27 の囲みの「旧名は仮定付きのまま残す」は、ノートのチャットが直す。）
