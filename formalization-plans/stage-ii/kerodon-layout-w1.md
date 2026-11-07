# Codex 指示書 KL-W1：∞ 圏のディレクトリを Kerodon の構成に合わせる（下書き）

作成：2026-11-07（段階 II の調整役）。状態：**下書き**。開始は Kerodon の対応表の確認（`research/kerodon-coverage/codex-review.md`）が全章終わり、main に入ってから。宛先：Codex（新しいチャット）。検収：調整役。
決定（11-07、ユーザー。調整役の推奨どおり）：時期・層・名前空間・細かさ・Kerodon にないものの置き場・範囲の六点（§0）。追加の決定として、Kerodon の Tag を宣言に付ける（§3）。

## 0. 目的と決定

`InfinityCategories/` の配置を Kerodon（https://kerodon.net）の章・節の構成に合わせる。Kerodon にない内容（HTT・HA 由来、プロジェクト固有）は、それとわかる置き場に分ける。どの宣言が Kerodon のどの項目かを、Tag で機械的に引けるようにする。

| 点 | 決定 |
| --- | --- |
| 時期 | **整理を先に**する。③ ∞ 供給と① ∞ 中核は、この束が main に入ってから始める。⑤ BS 実装と⑥ スキーム論は並行してよい（束が入ったら main を取り込み、改名表で追従する） |
| 層 | **Kerodon の配置を優先する（11-07 夜に改訂、ユーザー：「層の順序よりも移動を優先」）**。トップは `Kerodon/<Chapter>/<Section>/` と出どころ別の区分にし、今の層（`scripts/refactor/layers.json`：Core < … < F1 < F1B < F2 < …）は新しい配置に合わせて**組み直す**（layers.json と `layer_check.py` の規則を新しい構成で書き直す）。Kerodon の順と逆向きの依存は段 1 で一覧にし、置き場所の調整かファイルの分割で解く。Lean の import に循環は作れないので、解けないものだけ報告する |
| 名前空間 | **ディレクトリに合わせて変える**（F-2 の規約「名前空間＝ディレクトリ」を保つ）。旧名は deprecated alias で残し、改名表を利用側（BS・KST・CLMST・drafts）へ回す。仕組みは F-2 と同じ |
| 細かさ | **節（Section、a.b）まで**をディレクトリにする。名前は Kerodon の見出しの英語（UpperCamelCase）。Subsection（a.b.c）はファイル名か module docstring で示す。番号は版で変わりうるので、ディレクトリ名に番号を入れない。対応は Tag で持つ |
| Kerodon にないもの | **出どころ別に分ける**。各層の中で `Kerodon/`（Kerodon の章・節）と、`HTT/`・`HA/`・`Project/`（プロジェクト固有の補助）などを並べる。具体的な区分は段 1 で提案 |
| 範囲 | `InfinityCategories/` の全体と、**ほかのディレクトリに散らばった Kerodon の内容**（KST の S 構成・ProExcision の Alexander–Whitney と shuffle、`KST/LocalizingInvariants/LocalizationResolution` の局所化の存在、HomotopicalAlgebra・CategoryTheory・EInfinity の該当部分など。`research/kerodon-coverage/items.csv` と `review/ch*.csv` で、InfinityCategories の外の宣言を拾う）。**外から移すものも、層の順序より移動を優先する**：移すファイルが依存する外のファイル（の Kerodon に当たる部分）も一緒に移すか分割する。依存の閉包が大きすぎる・K 理論の本体まで引きずるものは、段 1 で候補として挙げて判断を仰ぐ |

## 1. 前提と材料

- Kerodon の対応表：`research/kerodon-coverage/items.csv`（3,553 項目）と、Codex の確認の結果 `research/kerodon-coverage/review/ch<N>.csv`（項目ごとの正しい宣言名）。目次は `toc.md`（Section と Subsection の Tag）。
- 段階 I の道具：`scripts/refactor/`（`layer_check.py`、`layers.json`、`merge_modules.py`・`split_module.py`、保存比較 `decl_snapshot.lean`・`compare_snapshots.py`・`snapshot_batch.py`、`check_deprecated_aliases.lean`、改名表 `targets/f-namespace-map.json` の形）。F-2 の進め方は `formalization-plans/archive/` の IF-F の記録。
- 規則：`formalization-plans/coordination.md` §2、計画 §4（新しい数学は書かない。既存の宣言の本文・型を変えない。名前の変更は alias つき。保存比較 v3b）。

## 2. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| **段 0** | **項目ごとの Tag の表**を作る。Kerodon の Subsection のページから、項目（a.b.c.d）ごとの Tag を取り直し、`research/kerodon-coverage/item-tags.csv`（number・kind・tag）に置く。11-06 の抜き出しでは項目ごとの Tag が不正確だったので、ページの各項目の見出しのリンクから取る | 停止点 0（表の件数と抜き取りの照合） |
| **段 1（計画）** | (a) **割り当て表**：`InfinityCategories/` の全ファイルと、外から移す候補のファイルを、行き先（`<層>/Kerodon/<Chapter>/<Section>/`、または `<層>/HTT/…`・`<層>/HA/…`・`<層>/Project/…`）に割り当てる。根拠は、そのファイルの宣言が対応表のどの項目か、と docstring の引用。一つのファイルが複数の節にまたがるときは、主な節に置くか分割するかを提案する（分割は既存の `split_module.py`）。(b) **ディレクトリの木**の案（見出しの英語の名前、出どころの区分の名前）。(c) **逆向きの依存**の一覧（Kerodon で後の節に置かれるファイルを、前の節のファイルが import するもの）と、それぞれの解き方の案（置き場所の調整・ファイルの分割）。(d) 外から移す候補と、一緒に移す必要のある依存の閉包。(d′) 新しい配置に合わせた layers.json の案（層の名前・順序・許す import の向き）。(e) 規模（動かすファイル数、名前空間が変わる宣言の数、alias の数、再ビルドの見込み） | **停止点 1**：調整役とユーザーが木と割り当てを確かめる。ここで止まる |
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
