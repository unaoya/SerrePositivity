# Codex 指示書 KL-W1：∞ 圏のディレクトリを Kerodon の構成に合わせる（下書き）

作成：2026-11-07（段階 II の調整役）。状態：**段 0・段 1 を開始（11-07 夜、ユーザー）**。段 2 以降は、Kerodon の対応表の確認（`research/kerodon-coverage/codex-review.md`）が全章終わり、main に入ってから（§5）。宛先：Codex（新しいチャット）。検収：調整役。
決定（11-07、ユーザー。調整役の推奨どおり）：時期・層・名前空間・細かさ・Kerodon にないものの置き場・範囲の六点（§0）。追加の決定として、Kerodon の Tag を宣言に付ける（§3）。

## 0. 目的と決定

`InfinityCategories/` の配置を Kerodon（https://kerodon.net）の章・節の構成に合わせる。Kerodon にない内容（HTT・HA 由来、プロジェクト固有）は、それとわかる置き場に分ける。どの宣言が Kerodon のどの項目かを、Tag で機械的に引けるようにする。

| 点 | 決定 |
| --- | --- |
| 時期 | **整理を先に**する。③ ∞ 供給は、この束が main に入ってから始める（① ∞ 中核は K と一緒に後回し）。⑤ BS 実装と⑥ スキーム論は並行してよい（束が入ったら main を取り込み、改名表で追従する） |
| 層 | **Kerodon の配置を優先する（11-07 夜に改訂、ユーザー：「層の順序よりも移動を優先」）**。トップは `Kerodon/<Chapter>/<Section>/` と出どころ別の区分にし、今の層（`scripts/refactor/layers.json`：Core < … < F1 < F1B < F2 < …）は新しい配置に合わせて**組み直す**（layers.json と `layer_check.py` の規則を新しい構成で書き直す）。Kerodon の順と逆向きの依存は段 1 で一覧にし、置き場所の調整かファイルの分割で解く。Lean の import に循環は作れないので、解けないものだけ報告する |
| 名前空間 | **ディレクトリに合わせて変える**（F-2 の規約「名前空間＝ディレクトリ」を保つ）。旧名は deprecated alias で残し、改名表を利用側（BS・KST・CLMST・drafts）へ回す。仕組みは F-2 と同じ |
| 細かさ | **節（Section、a.b）まで**をディレクトリにする。名前は Kerodon の見出しの英語（UpperCamelCase）。Subsection（a.b.c）はファイル名か module docstring で示す。番号は版で変わりうるので、ディレクトリ名に番号を入れない。対応は Tag で持つ |
| Kerodon にないもの | **出どころ別に分ける**。`InfinityCategories/` の直下に `Kerodon/`（Kerodon の章・節）と、`HTT/`・`HA/`・`Project/`（プロジェクト固有の補助）などを並べる（11-07 夜の改訂で、層の中ではなく直下に）。具体的な区分は段 1 で提案 |
| 範囲 | `InfinityCategories/` の全体と、**ほかのディレクトリに散らばった Kerodon の内容**（KST の S 構成・ProExcision の Alexander–Whitney と shuffle、`KST/LocalizingInvariants/LocalizationResolution` の局所化の存在、HomotopicalAlgebra・CategoryTheory・EInfinity の該当部分など。`research/kerodon-coverage/items.csv` と `review/ch*.csv` で、InfinityCategories の外の宣言を拾う）。**外から移すものも、層の順序より移動を優先する**：移すファイルが依存する外のファイル（の Kerodon に当たる部分）も一緒に移すか分割する。依存の閉包が大きすぎる・K 理論の本体まで引きずるものは、段 1 で候補として挙げて判断を仰ぐ |

## 1. 前提と材料

- Kerodon の対応表：`research/kerodon-coverage/items.csv`（3,553 項目）と、Codex の確認の結果 `research/kerodon-coverage/review/ch<N>.csv`（項目ごとの正しい宣言名）。目次は `toc.md`（Section と Subsection の Tag）。
- 段階 I の道具：`scripts/refactor/`（`layer_check.py`、`layers.json`、`merge_modules.py`・`split_module.py`、保存比較 `decl_snapshot.lean`・`compare_snapshots.py`・`snapshot_batch.py`、`check_deprecated_aliases.lean`、改名表 `targets/f-namespace-map.json` の形）。F-2 の進め方は `formalization-plans/archive/` の IF-F の記録。
- 規則：`formalization-plans/coordination.md` §2、計画 §4（新しい数学は書かない。既存の宣言の本文・型を変えない。名前の変更は alias つき。保存比較 v3b）。

## 2. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| **段 0** | **項目ごとの Tag の表**を作る。Kerodon の Subsection のページから、項目（a.b.c.d）ごとの Tag を取り直し、`research/kerodon-coverage/item-tags.csv`（number・kind・tag）に置く。11-06 の抜き出しでは項目ごとの Tag が不正確だったので、ページの各項目の見出しのリンクから取る | 停止点 0（表の件数と抜き取りの照合） |
| **段 1（計画）** | (a) **割り当て表**：`InfinityCategories/` の全ファイルと、外から移す候補のファイルを、行き先（`InfinityCategories/Kerodon/<Chapter>/<Section>/`、または `InfinityCategories/HTT/…`・`HA/…`・`Project/…`）に割り当てる。根拠は、そのファイルの宣言が対応表のどの項目か、と docstring の引用。一つのファイルが複数の節にまたがるときは、主な節に置くか分割するかを提案する（分割は既存の `split_module.py`）。(b) **ディレクトリの木**の案（見出しの英語の名前、出どころの区分の名前）。(c) **逆向きの依存**の一覧（Kerodon で後の節に置かれるファイルを、前の節のファイルが import するもの）と、それぞれの解き方の案（置き場所の調整・ファイルの分割）。(d) 外から移す候補と、一緒に移す必要のある依存の閉包。(d′) 新しい配置に合わせた layers.json の案（層の名前・順序・許す import の向き）。(e) 規模（動かすファイル数、名前空間が変わる宣言の数、alias の数、再ビルドの見込み） | **停止点 1**：調整役とユーザーが木と割り当てを確かめる。ここで止まる |
| **段 2（Tag）** | 対応表で `own`・`both` と確かめた宣言（`review/ch<N>.csv` の `ok`・`fix` のうち SerrePositivity のもの）に `@[kerodon TAG]` を付ける（Mathlib の `Mathlib.Tactic.CrossRefAttribute`。docstring に Kerodon へのリンクが自動で足される）。`partial` の宣言には付けず、docstring に「Kerodon a.b.c.d（Tag XXXX）の特別な場合」のように書く。既存の docstring の「Kerodon a.b.c.d」の引用には「（Tag XXXX）」を添える。番号のずれ（`README.md` の一覧）もここで直す。`#kerodon_tags` の出力を `research/kerodon-coverage/kerodon-tags-lean.txt` に保存し、対応表と突き合わせる | 停止点 2（付けた件数、突き合わせの差） |
| **段 3（移動）** | 段 1 の承認された割り当てで、ファイルを動かし、import 行を書き換え、名前空間を付け替える（旧名は deprecated alias）。新しい layers.json と `layer_check.py` の規則・入口ファイル・監査（`scripts/audit_*.lean`）・`InfinityCategories/README.md` を更新する。改名表を `scripts/refactor/targets/kl-namespace-map.json` に置く。保存比較 v3b で、移動の前後で宣言の型と本文が一致することを示す | **停止点 3**：保存比較の未説明 0、対象のビルド。下流ビルドと verify は調整役の合図で |
| 段 4 | 下流ビルドと verify（調整役の暦）。BS・KST・CLMST・drafts の利用側の import と名前を改名表で書き換える（BS・drafts の分は調整役が確かめる） | 停止点 4：取り込み |

- 段 2 と段 3 はどちらも多くのファイルを書き換える。全体の再ビルドを一回にするため、**段 2 と段 3 は一つの束にし、下流ビルドと verify は段 3 の後に一回だけ**行う（段 2 の途中は、触ったモジュールだけの小さなビルド）。
- 段 1 の承認の前に、ファイルを動かさない。

## 3. Kerodon の Tag の付け方（ユーザーの追加の決定、11-07）

- 主な手段は Mathlib の属性 `@[kerodon TAG]`（`@[kerodon TAG "短い注記"]` も可）。宣言の docstring に Kerodon へのリンクが自動で付き、`#kerodon_tags` で全一覧を出せる。
- Tag は項目（a.b.c.d）の Tag（段 0 の表）。Subsection や Section の Tag は、ファイルの module docstring に「Kerodon a.b.c（Tag XXXX）」の形で書く。
- 一つの宣言が複数の項目に当たるときは、属性を複数付けてよい。
- 補助の補題（Kerodon の項目そのものではないもの）には属性を付けない。module docstring の Tag で足りる。

## 4. 共通の規則

1. 新しい数学は書かない。既存の宣言の本文と型は変えない。名前と置き場所だけを変え、旧名は alias で残す。
2. sorry・公理・新しい引用を足さない。
3. 段 3 の移動は一つの枝で、こまめにコミットする。main の作業木では作業しない。取り込みは調整役。
4. ビルドは、束の途中は触ったモジュールだけ（`with_build_lock.sh` を通す）。下流ビルドと verify は調整役の合図で一回。
5. 報告は段ごとに：件数、ビルド・保存比較・監査の結果、判断が要る点。

## 5. 追記（2026-11-07 夜、調整役）：段 0・段 1 を先に始める

ユーザー決定：Kerodon の確認の完了を待たずに、**段 0 と段 1 を今から始める**（③ ∞ 供給と BS の ∞ 側を待たせる時間を縮めるため）。段 0・段 1 は報告だけの段で、Lean のファイルは動かさない。

1. **worktree と枝**：main の最新から `../SerrePositivity-kerodon-layout`（`LEAN_Projects.nosync/` の下）、枝 `refactor/kerodon-layout`。書いてよいのは `research/kerodon-coverage/` の下（`item-tags.csv` など）と、`formalization-plans/stage-ii/` の下の計画と報告のファイル（`kerodon-layout-w1-report.md`、割り当て表 `kerodon-layout-assignment.csv` など）だけ。`SerrePositivity/` の Lean と `scripts/` は段 3 まで触らない。
2. **段 0**：§2 のとおり。Kerodon の Subsection のページ（取得済みの目次 `research/kerodon-coverage/toc.md` の Tag）から、項目ごとの Tag を取り直す。抜き取りで 50 件ほど照合する。
3. **段 1 の材料**：Kerodon の確認は進行中（Ch 1 は `research/kerodon-coverage/review/ch1.csv`、Ch 2 以降はまだ）。割り当て表は、確認済みの章は `review/ch<N>.csv` の宣言名を、まだの章は元の `items.csv` の宣言名と、ファイルの docstring の Kerodon の引用（9,711 件、`citations-summary.md`）を使って作る。**確認が済んでいない章の割り当てには印を付ける**（`basis` 列に `review` か `items`）。確認が全章終わったら、段 2 の前に割り当て表を一度だけ見直す。
4. **段 1 の報告**：§2 の (a)〜(e) と (d′)。特に、層の順序より移動を優先する方針（§0 の層・範囲の行）で、逆向きの依存の解き方と、外から移す候補の依存の閉包を具体的に書く。依存の閉包が大きすぎるもの・K 理論の本体まで引きずるものは、候補として挙げて止まる。
5. **ビルド**：段 0・段 1 ではビルドしない。依存の調べは import 行の静的な解析（`scripts/refactor/` の道具、または自前の Python）で行う。
6. **停止点**：停止点 0 は報告して承認を待たずに段 1 に進んでよい。**停止点 1 で必ず止まる**（調整役とユーザーが木と割り当てを確かめる）。

## 6. 追記（2026-11-07 15:40、調整役）：Tag の対象から外す宣言

型に満たせない仮定（`[ModelCategory SSet]` など）を持つ宣言には、段 2 で `@[kerodon TAG]` を付けない。一般の圏にモデル圏構造を仮定する宣言は、Kerodon の確認（`research/kerodon-coverage/codex-review.md` §6）で、使われる具体的な圏に instance が実在すると確かめられたものだけを対象にする。段 1 の割り当て表では、これらの宣言に印を付ける（`basis` 列とは別に `model_category` 列など）。

## 7. 追記（2026-11-07 夕、調整役）：停止点 1 の決定

報告 `kerodon-layout-w1-report.md` と付表（割り当て表・逆向きの import・外の候補・層の案・モデル圏の印）を確かめた。ユーザー決定：

1. **名前空間と alias**：名前空間はディレクトリに合わせて変える。`InfinityCategories/` の中の参照は機械的に書き換え、**deprecated alias は ∞ 圏の外（BS・KST・CLMST・EInfinity・HomotopicalAlgebra・Paper・drafts・走っているレーンの枝）から使われている名前だけ**に付ける（全部に付けると約 5.5 万になるため）。外の参照も、main にあるものは同じ束で書き換え、alias は走っている枝と drafts のためのものとする。
2. **外から移す候補**：そのまま移せる 4 群だけを移す（§2.5 の Alexander–Whitney・shuffle・EZ、§6.3.2 の局所化の存在、§7.1.8 の関手圏の各点ごとの余極限、§3.3 の Ex∞）。K 理論の本体に届く 7 本と、依存の閉包が大きい 21 本は今の場所に残す。
3. **時期**：段 2・段 3 は、Kerodon の確認（Ch 2〜10）が終わってから。そのとき、推定による割り当て（`topic-confirm`・`origin-confirm`、約 12,400 本）を、確認の結果で一度だけ見直してから移す。
4. **層**：報告の (d′) の、ファイル単位で層を指定する 5 段の案（SharedFoundation・Portable・Comparison・Entrypoints・Consumers）を採る。ディレクトリは Kerodon の構成を表し、依存の順序はファイルごとに `layer_check.py` で検査する。

**それまでにしてよいこと（段 1.5、道具の準備）**：段 3 で使う道具を、`scripts/refactor/` の**新しいファイル**として作り、テストする。既存のスクリプトと `SerrePositivity/` の Lean は触らない。

- ∞ 圏の中の参照の機械的な書き換え（名前空間の付け替えに合わせて、`open`・完全修飾・相対名を正しく直す）。
- 外から使われている名前の一覧の抽出と、その名前だけの alias の生成（F-2 の `deprecated_alias` の仕組み）。
- ファイル単位の層の指定と、それを検査する `layer_check.py` の新しい版（今の版は残し、別のファイルとして）。
- 割り当て表の見直しの手順（確認の結果 `review/ch<N>.csv` を読み、`basis` を更新し、配置の変わる行を一覧にする）。

段 1.5 の結果は報告に書き、枝にコミットする（停止点 1.5、報告して待たずに続けてよい）。ビルドは道具のテストに要る小さなものだけ（鍵を通す）。

## 8. 追記（2026-11-10、調整役）：段 2・段 3 を始める

Kerodon の確認（全 10 章のやり直し）と抜き取りが main に入った（a12e53be8）。own・both・mathlib は、全章で比較の後の差が 0 件（`research/kerodon-coverage/codex-review.md` §8.3・§8.4、`review/check/cross-*.md`）。partial・none は基準を §8.1 で絞り、最後に一括で見直す（第 4・5 章の partial・none は未確定）。これを受けて段 2・段 3 を始める。

1. **段 1.6（割り当ての見直し）**：`klw1_review_assignment.py` を正式モード（`--accept-cross-review`）で流し、`changes.csv` を出す。**停止点 1.6**：件数（行き先が変わる行、撤回、新しい対応元、パスの衝突）と、行き先が変わる行の一覧を報告して止まる。調整役が確かめてから段 2 へ。
   - 割り当ての根拠には own・both・mathlib の行だけを使う。partial・none の行は、ファイルの行き先を変える根拠にしない（一括見直しで変わりうるため）。partial を根拠にしている既存の割り当ては、そのままにして印を付ける。
2. **段 2（Tag）**：`@[kerodon TAG]` は own・both の SerrePositivity の宣言だけに付ける（§3、§6）。**partial の宣言への「の特別な場合」の注記は今は書かない**（一括見直しの後）。既存の docstring の「Kerodon a.b.c.d」に「（Tag XXXX）」を添える作業はしてよい（`item-tags.csv`）。
3. **段 3（移動）**：§2 のとおり。段 2 と一つの束にし、下流ビルドと verify は段 3 の後に一回（調整役の暦）。
4. **走っている枝（⑤a・⑤b・⑥、HA・HTT・K の地図）**：段 3 の取り込みの時に、モジュールの改名表（`kl-module-map.json`、旧モジュール → 新モジュール）と名前の改名表（`kl-namespace-map.json`）を main に置き、各レーンが自分の枝の新しいファイルの import と名前を書き換える。そのための書き換えの一行コマンド（`klw1_namespace.py rewrite` を枝の新しいファイルだけに当てる手順）を、停止点 3 の報告に書く。alias は名前だけなので、import の行は各レーンが直す必要がある。

## 9. 追記（2026-11-10、調整役）：停止点 1.6 の承認

**承認**：停止点 1.6（`kerodon-layout-w1-report.md` の「停止点 1.6」、`kerodon-layout-stop-1-6/changes.csv`）。行き先が変わる 22 行、根拠の撤回 172 行（行き先は変えない）、新しい対応元 4 本（表に足さない）、partial を根拠に維持した 437 行（印つき）の扱いは、報告のとおりでよい。段 2 に進んでよい。段 2・段 3 は一つの束で、停止点 3 まで止まらずに進めてよい（§2 の条件：保存比較の未説明 0、対象のビルド）。

一つだけ規則を足す：**主な内容が Kerodon の外のファイル**。module docstring の主な主題が HTT・HA の項目（例：`F2/Presentable/Definition.lean` は表現可能な ∞ 圏の定義、HTT 5.5.1）で、Kerodon の項目に当たる宣言がその一部だけ（例：同じファイルの `HasSmallColimits`・`HasSmallLimits`、Kerodon 7.6.6.1）のときは、

1. 分割が素直なら（その宣言を使う側が少なく、`split_module.py` で切れる）、Kerodon の項目の部分を `Kerodon/<章>/<節>/` へ、残りを `HTT/…`・`HA/…` へ分ける。
2. 分割が素直でなければ、ファイルは `HTT/…`・`HA/…` に置き、Kerodon の宣言には `@[kerodon TAG]` だけを付ける。

22 行のうち `F2/Presentable/` の 4 本（Definition、AccessibleFunctor、EquivalenceColimits、Duality/RightUnitContractible）はこの規則で確かめ、ほかにも当たるファイルがあれば同じにする。どれをどう扱ったかを停止点 3 の報告に書く。
