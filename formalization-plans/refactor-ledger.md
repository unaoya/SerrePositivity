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
