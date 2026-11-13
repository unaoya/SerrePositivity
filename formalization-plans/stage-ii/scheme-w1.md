# Codex 指示書 SC-W1：スキーム論の土台（公理 (3) の再確認、平坦化、BS17 Thm 4.1 (i)）

作成：2026-11-05 夜（段階 II の調整役）。宛先：⑥ スキーム論レーンの Codex（新しいチャット）。検収：調整役（設計判断はユーザーと決める）。
正本：[段階 II の計画](../stage-ii-plan-draft.md) §1.5（スキーム論の土台）・§2（B-5）・§5.1。BS17 の調査は [citations-survey-2026-11-05.md](../bhatt-scholze/citations-survey-2026-11-05.md) §3。K の経路は [infinity-lanes/foundations.md](../infinity-lanes/foundations.md) §3 と [kst-lanes/k-theory-kst-route.md](../kst-lanes/k-theory-kst-route.md)。規則は [coordination.md](../coordination.md) §2 と計画 §4。

## 0. 目的

BS（目標 A）と K（目標 B）の両方が使う代数幾何の土台を作る。段階 II の終わりの条件は sorry 0 で、BS で引用の予定だった [BS17, Thm 4.1 (i)]（完全環の v 降下）も原典どおり証明する（11-05 夜、ユーザー決定）。その土台の多くは K の B-5（ブローアップ、平坦化、準連接コホモロジー）と共通である。
1. **公理 (3)（冪零不変性）の供給経路を決めるための調査**（Lean は書かない）。
2. **スキーム論の土台**：休止中の K-L7 の残り（平坦化など）、続いて BS17 に要る部品、最後に BS17 Thm 4.1 (i) の affine・O の場合。

## 1. 準備

1. main（f3fcefe8e 以降）から worktree `../SerrePositivity-scheme`（`LEAN_Projects.nosync/` の下）と枝 `math/scheme` を切る。`source ~/.zshenv` の後、`lake env | grep LAKE_ARTIFACT_CACHE` でキャッシュが効いていることを確かめ、`lake build SerrePositivity.KST.SchemeLemmas` で温める。
2. F-2 で名前空間が変わった宣言は、改名表 `scripts/refactor/targets/f-namespace-map.json` の新しい名前を使う（旧名の deprecated alias は新しいファイルでは使わない）。
3. main の大きな束が入るたびに main を取り込む（調整役が知らせる。衝突は main 側を正に）。

## 2. 段 1：公理 (3) の供給経路の再確認（報告だけ）

**背景**：Thm 3.1 の八公理のうち (3)（冪零不変性）は、v1 の D ブロック（⊗ℚ の五項補題と、離散的な冪零不変性 D9）で供給する予定だった。D9 の Step 2 は D2（連結 dg 代数の GL と、Waldhausen 2.3.2 の ∞-S• 版の比較定理。群完備化と plus 構成）を使う。ところが計画 v2（Land–Tamme 経路、10-19）では L2 の plus 構成を「不要」として凍結した。このため (3) の経路は v2 で未決のまま残った（foundations.md §3 の 4）。

**調べること**（原典と既存コードを読んで報告。Lean は書かない）：
1. Lean 側で公理 (3) が何を要求しているか。`theorem_3_1_K0` と `Section4.supportedRankK0_descent` の型、八公理の形式化（`KST/Descent/` など。L8 の記録 `formalization-plans/archive/L8-descent-log.md` に「公理 (3) の幾何学的な型」がある）から、(3) の正確な主張（どの環・どの K・係数・次数）を書き出す。
2. 候補の経路を比べる。各経路について、要る基盤（既存か、どのレーンが作るか）、引用の有無（**K 理論側は引用なしが段階 II の条件**）、規模の見込みを書く。
   - (a) D9 のまま：D2（GL と plus 構成）を凍結した L2 のコードから使う。L2 の既存コードがどこまであるか（凍結の状態、sorry の有無）。
   - (b) Land–Tamme で処理する：LT の Cor 3.5（冪零不変性。経路の記録 §「LT Thm A.2 の証明で ⊙ を使う箇所」）か、⊙ と pro 切除（B-4）から (3) を得る。⊗ℚ と E = fib(K_ℚ → K[1/p]_ℚ) の形で足りるか。
   - (c) ほかに見つかった経路（Goodwillie の定理は引用になるので、使うなら証明の規模も）。
3. 推奨と、その理由。決められない点はユーザーに聞く形の問いにする。

**止めて報告（停止点 1）**：上の 1〜3 を `formalization-plans/stage-ii/scheme-axiom3-report.md` に書いて `math/scheme` にコミットし、要約を報告する。調整役がユーザーと経路を決める。**段 2 はこの報告の後、承認を待たずに始めてよい**（段 2 は (3) の経路に依存しない）。

## 3. 段 2：スキーム論の土台（Lean）

前半は休止中の K-L7 の残り（[kst-lanes/L7-scheme-lemmas.md](../kst-lanes/L7-scheme-lemmas.md) の「残り」）。既存のコードは `KST/SchemeLemmas/`（例：`NoetherianFiniteModuleFlattening.lean`）と `KST/Descent/GenericFiniteFlattening.lean`。後半は BS17 の証明（arXiv:1507.06490 の §2〜§4）と、その芯の [BST13, Lemma 3.9]（Gabber、arXiv:1307.3763 §3）。

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| 2a | 現状の照合：L7 の引き継ぎ（10-19）の後に何が main に入ったか、F-2 の後の名前と置き場所、残りの各項目の前提。あわせて、2e〜2h に要る Mathlib の材料（準連接層、層のコホモロジー、固有射、Noether 近似 `AffineTransitionLimit`・`SpreadingOut` など）の有無を確かめ、2e〜2h の紙の筋と規模を報告 | **停止点 2a**：調整役が 2e〜2h の範囲を確かめる。2b〜2d は承認を待たずに進めてよい |
| 2b | Stacks 051R（多項式商の局所化とテンソル基底変更の比較 → 有限型代数の一般自由性）、続いて Stacks 05FS（Lemma 38.9.2、一般自由性・Noether 帰納法で代数の射影性の存在を完成） | **停止点 2b**：調整役が取り込む |
| 2c | KST Prop 5.2（鳩ノ巣による共通冪、核の消滅、Artin–Rees による交わりの消滅）、Huneke–Swanson 8.1.5・8.2.1 と KST Lemma 5.6 の古典部分（Rees 拡大の整性・有限性から有限射） | **停止点 2c** |
| 2d | Stacks 0811・0810（相対 Noether 正規化と台の次元による devissage → 一般の有限型加群の平坦化）、Stacks 081T（Lemma 38.31.4、Temkin 2008 Lemma 2.1.5：平坦化の中心を strict transform と大域の貼り合わせへ）。BS17 Lemma 2.6 が使う [RG71, 5.2.2] の形（固有な全射をブローアップと fppf で細分）が得られるかも確かめる | **停止点 2d** |
| 2e | BST13 Lemma 3.9 の土台：準連接層のコホモロジー（affine での消滅、Čech での計算）、固有射のコホモロジーの有限性、コホモロジー版の Artin–Rees（Stacks 02O7）、Stein 分解 | 停止点 2e（段の途中でも区切りのよい所で報告） |
| 2f | BST13 Lemma 3.5〜3.9：O_perf の位相不変性、有限射の場合（完全環の弱正規性。Kollár の商は使わなくてよい）、Lemma 3.9 の (1)（高次）と (2)（H⁰） | 停止点 2f |
| 2g | BS17 §2：v 被覆（Def 2.1、affine 版）、Rydh Thm 3.12（[Ryd10]、有限表示の v 被覆は開被覆 ∘ 固有な全射で細分できる）、Lemma 2.6（帰納的なレベル）、Thm 2.9・Lemma 2.12・Cor 2.14 を複体の言葉で述べ直したもの（前層が「Čech 複体がすべての次数で完全」になる被覆の類が、fppf・抽象ブローアップの四角形・余フィルター極限で閉じること。集合値の層の条件は H⁰ しか出ないので不足。∞ 圏は使わない形で書けるかを 2a で判定し、無理なら止めて報告） | 停止点 2g |
| 2h | BS17 Thm 4.1 (i) の n = 1・E = O の場合：Prop 4.5、Lemma 3.4（完全化と平坦性）、Lemma 4.6 (i)。一般の主張として `AlgebraicGeometry/` に置く。drafts の `cech_exact_of_vCover_perfect`（`formalization-plans/bhatt-scholze/drafts/A6/ArcSheafProperty.lean:108`）の型を閉じられる形にする（⑤ BS 実装が drafts をこれで閉じる） | **停止点 2h**：調整役が取り込み、⑤に知らせる |

- KST Remark 3.3 と Lemma 5.5 の幾何の入力は、導来 blowup の対象（K 理論レーン）が決まってから。ここでは扱わない。
- 時間の目安：2b は 10〜25 時間、2c は 12〜28 時間、2d は 24〜60 時間（L7 の記録）。2e〜2h は 2a の報告で見積もる（調査の粗い見積もりは全体で 5〜15 万行規模）。条件付きの中心存在を「一般の平坦化の完成」と呼ばない（L7 の注意）。
- 数学的に詰まったら、通ったところまで（ビルドが通り sorry 0 の補題）を報告して止める。未完の Lean は main に入れない（枝 `math/scheme-wip` に置く）。

## 4. 共通の規則

1. 新しい数学は**新規ファイルだけ**。置き場所：2b〜2d の L7 の続き（既存の `KST/SchemeLemmas/` のファイルの直接の続き）は `KST/SchemeLemmas/`。BS と K が共有するスキーム論（2e〜2h と、2b〜2d のうち K に依存しない一般論）は新設の `SerrePositivity/AlgebraicGeometry/`（名前空間 `SerrePositivity.AlgebraicGeometry`、KST・BhattScholze・InfinityCategories を import しない）。最初のファイルを置くときに、入口 `AlgebraicGeometry.lean`・ルートへの登録・監査 `scripts/audit_algebraic_geometry.lean` を作る。K に依存しない可換環論で一般性のあるものは `CommutativeAlgebra/` の新しい下位ディレクトリ（BS 実装も `CommutativeAlgebra/` に置くので、既存の下位ディレクトリには足さない）。既存の宣言の本文・型・名前は変えない（要るときは止めて報告。処置は判断表の範囲で、保存比較 v3b）。
2. sorry・公理・新しい引用を残さない。Mathlib にあるものは Mathlib を使う（同じ主張を作り直さない）。
3. ビルドは小さなビルドだけ（変更したファイルと直接の importer）。始める前に `ps -axo command= | grep '[l]ake build'` が空で、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build …` で鍵が取れること。全ビルド（下流・verify）はしない。
4. 新規モジュールは入口（`KST/SchemeLemmas.lean` など）と該当する監査に登録する（`importModules` を使う監査は `import` 行にも書く）。監査は単独で流す。
5. main の作業木では編集もビルドもしない。main への取り込みは調整役が行う。
6. docstring は日本語の 概要／方針／規約／使われ方。
7. 報告は段ごとに：ビルドの結果、監査、追加した宣言の名前と主張（言葉で一行ずつ）、残っている一歩、コミット。

## 5. 条件付きの事前承認

段 2b〜2d は、「対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない」なら、停止点で報告したうえで承認を待たずに次の段へ進んでよい。2e 以降は停止点 2a で調整役が範囲を確かめてから。2e〜2h の各段も同じ条件で次へ進んでよい。取り込みは調整役が停止点ごとに行う。

## 6. 追記（2026-11-07、調整役）：BS17 の経路に絞る

ユーザー決定（11-07）：K 理論は後回しにし、当面は Kerodon との対応の整理・∞ 圏の整備・BS に集中する。このレーンは **BS17 Thm 4.1 (i)（完全環の v 降下）の経路だけ**を進める。

- **段 1（公理 (3) の調査）は行わない**（K 用。K の計画を見直すときに改めて出す）。
- **段 2c（KST Prop 5.2、Huneke–Swanson と KST Lemma 5.6）は行わない**（K 用）。
- 段 2a は、BS17 の経路に要る範囲の照合と紙の筋に絞る（BS17 Lemma 2.6 が要る平坦化、BST13 Lemma 3.9、Rydh Thm 3.12、判定法）。
- 段 2b・2d（平坦化）は、**BS17 Lemma 2.6 に要る形**（固有な全射をブローアップと fppf で細分する [RG71, 5.2.2] の形、Noether 近似、generic flatness）に絞る。K の L7 の残りのうち、それに要らないものは後回し。
- 段 2e〜2h はそのまま。
- 開始：今すぐ始めてよい（KL-W1 とは触る場所が重ならない：`KST/SchemeLemmas/` の続きと新設の `AlgebraicGeometry/`）。

## 7. 追記（2026-11-07、調整役）：停止点 2a の承認と、KST/SchemeLemmas の移動（案 (a)、ユーザー承認）

**承認**：段 2a の照合と紙の筋（平坦化の不足、非 Noether の v 被覆の細分案、第一象限の二重複体による全次数の判定、BST13 Lemma 3.9 の H⁰ で Stein 分解を省く案）。

**置き場所の決定（案 (a)）**：`KST/SchemeLemmas/`（345 本）は KST のほかの部分にも K 理論にも依存しない（import は自身・Mathlib・CommutativeAlgebra だけ。外の importer は KST/Descent の 7 本と KST/DerivedBlowup の 1 本）。これを丸ごと `AlgebraicGeometry/` の下へ移す。

1. **移動の束（段 2a′）**：段 2b の新しい数学とは別のコミットにする。
   - 行き先：`SerrePositivity/AlgebraicGeometry/` の下。中の下位ディレクトリの構成は今のまま保つか、内容に合わせた名前にするかを、移動の前に表で示す（`scripts/refactor/targets/sc-namespace-map.json` に旧モジュール名 → 新モジュール名、旧名前空間 → 新名前空間の表）。
   - 名前空間はディレクトリに合わせて付け替え（F-2 の規約）、旧名は deprecated alias で残す（F-2 と同じ仕組み、`scripts/refactor/` の道具を使う）。
   - import 行の書き換え：外の importer 8 本、ルート `SerrePositivity.lean`、監査 `scripts/audit_kst_scheme_lemmas.lean`（名前を `audit_algebraic_geometry.lean` に変えて統合してよい）。
   - 保存比較 v3b で、移動の前後で宣言の型と本文が一致することを示す（未説明 0）。
   - ビルド：移したモジュールと直接の importer の小さなビルド。ルートと下流の全ビルドは調整役の合図で一回。
   - **停止点 2a′**：表と保存比較の結果、対象のビルド。ここで止まり、調整役が下流ビルドの合図を出してから取り込む。
2. **段 2b は並行して始めてよい**：新しいファイルのうち、`KST.SchemeLemmas` を import しないものは `AlgebraicGeometry/` に置く。import するものは、ひとまず `KST/SchemeLemmas/` に置く（移動の束で一緒に移る）。移動の束と 2b のコミットは分ける。
3. 以後、BS17 の経路の新しいファイルは `AlgebraicGeometry/` に置く。`AlgebraicGeometry/` は KST・BhattScholze・InfinityCategories を import しない。

## 8. 追記（2026-11-07 夜、調整役）：2e は射影の場合、Noether 近似のモデルは 2g で

段 2d の途中報告（de4af200d・ea79a738b）を受けて。

1. **2e は射影の場合に絞る**：BS17 Thm 2.9 の帰納で (ii) を使うのは、Lemma 2.6 で選ぶブローアップの Čech ファイバー冪と、閉厚化への底変換だけで、どちらも射影。したがって 2e は、Proj の標準開被覆と次数付き加群による射影版の有限性・形式関数（BST13 Lemma 3.9 の正次数の議論）でよい。一般の固有射のコホモロジーの有限性と Stein 分解は作らない。Thm 2.9 の十分性はこの範囲で直接実装する。
2. **Noether 近似のモデル構成は 2g に寄せる**：Lemma 2.6 の入力は有限表示なので、2g で Lemma 2.12 相当の有限型 F_p 上の被覆モデルを先に供給し、Lemma 2.6 の帰納を Noether 基底上で始める。2d に残っている「全射性の降下に渡すモデル構成と固有性の降下」は、2g の被覆モデルの構成と一つにまとめ、二重に作らない。
3. 2d の残り（étale 局所有限化で幾何学的整な成分を基底側に広げる、余核の次元帰納、局所中心を因子に含む基底側の中心）はそのまま。停止点 2d の目標は §3 の表のとおり、[RG71, 5.2.2] の形（固有な全射をブローアップと fppf で細分）。

## 9. 追記（2026-11-11、調整役）：原典の Hⁱ と Čech 版の接続 — 案 (b)

2e の作業メモ（`scheme-w1-2e-route.md` §「原典の Hⁱ と Čech 版の接続」、3fb937fc2）の二案のうち、**案 (b)** にする。

- **理由**：このレーンの最終出力は、affine な v 被覆の増大 Čech 余脈体の完全性 `SerrePositivity.Cech.AugmentedRingCechExact`（`HomologicalAlgebra/Cech/Basic.lean`）で、これ自体が原典の主張（affine の構造層の v 降下）の形である。射影的なブローアップ上の Hⁱ（BST13 Lemma 3.9 の核の評価と像の安定化、Stacks 30.20.4 の形式関数、BS17 Lemma 4.6 (i) の完全三角）は、その証明の途中の補題で、主張の定義を置き換えるものではない。途中の補題を、分離的なスキームのアフィン被覆の Čech で述べ、最終出力までつなげば原典どおりの方針に反しない。案 (a) の導来関手の層コホモロジーとの比較は、最終出力に使われないので作らない。
- **条件**：
  1. 途中の主張は名前と docstring で「Čech 版」と明記する（今の `CechHomology` の型のとおり）。docstring には、原典の Hⁱ の主張の番号と、「分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6、⑥ のメモの 01X8 の節）が、この比較は形式化しない」を書く。
  2. 被覆の取り方への依存を残さない：2g へ渡す前に、共通アフィン細分との比較、底変換、閉厚化、Frobenius、filtered colimit との整合性を示す（作業メモの案 (b) のとおり）。比較は射に自然な形にする。
  3. 最終出力の型（`AugmentedRingCechExact`）と、それを使う側の型は変えない。
- **宇宙**：作業メモの確認（有限生成の加群は `Module.Finite.small`・`Shrink.linearEquiv` で基底環の宇宙に移せる）で足りる。大きい型の入口が要るときに移送をつなぐ。


## 追記（2026-11-12 夜、調整役）：規模の上限の決め方の変更（ユーザー決定）

停止の基準は各段の段 0 の見込みの上端の **2 倍**（`coordination.md` §2）。各段の見込みの半分に達した時点で一度、止まらずに実測と残りの見込みを報告する。調整役がすでに明示した上限が 2 倍より高いときはその上限のまま。
2f は段取り（scheme-w1-2f-route.md）の上端 9,000 の 2 倍＝18,000 行。2g・2h は各段の段 0 の見込みから。

## 追記（2026-11-14、調整役）：停止点 2f と、2g の段 0 の扱い

停止点 2f（15753e53f、2f の追加 15,780 行、宇宙の一般化 69 宣言は外での利用 0）を受け取った。取り込みは B3 の取り込みの後（main は凍結中）。

2g の段 0（727d4cd9e、2g 16,300〜33,300 行、2h まで 18,300〜38,300 行）を受けて：
1. **G0（付値判定と有限族・一射の橋）は Lean に進む**（どちらの経路でも要る）。
2. 並べて紙で、**Rydh 3.10（fppf–proper の細分）で降下の消去を進める経路**を比べる：BS17 Thm 4.1 (i) の同じ主張に届くか、G1・G2 の縮み方、G3〜G5 の変わり方、見込みの行数。証明の経路の違いで、主張は変えない。
3. 比べた結果で G1 以降の経路と外枠を決める（上端が 2 万行を大きく超えるならユーザーに諮る）。
4. G1・G2（幾何の供給）の完成を停止点 2g-1、G3〜G5（Čech の判定と移送）の完成を停止点 2g-2 とし、それぞれ単独で取り込む。
