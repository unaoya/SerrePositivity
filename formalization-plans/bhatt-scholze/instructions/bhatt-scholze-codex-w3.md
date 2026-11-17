# Codex 作業指示書 BS-W3：B4（Thm 7.4）の証明を原典どおり André 経由にし、B4 固有の構成を RootEnvelope/ に残す

作成：2026-10-25（BS 作業チャット）。宛先：Codex。BS-W2 のコミット（`c9d5fea53`・`6c13fe6be`）の後に行う。
決定の経緯は勉強ノート第 7 章の BR9（`exposition/ja/bs/07-semiperfectoid.html`）。ユーザーの決定（10-25）：
「証明を原典に揃える。不要になったコードで役に立ちそうなものは残す」。

## 0. 前提と全体の方針

- 前提は BS-W1 の §0 と同じ（所有範囲、他レーンの並行作業、root ビルドの禁止、`git add -A`・`git commit -a` の禁止）。
  所有範囲に `scripts/audit_andre_*.lean` を含める。
- B4 の公開定理 `surjective_of_isPerfectoidization_of_semiperfectoid_quotient` の**名前と型は変えない**。証明だけを、
  原典の Thm 7.4 の証明（André の補題で絶対整閉な perfectoid 環へ p 完全忠実平坦に拡大し、そこで全射性を得て降下する）に替える。
- これまでの B4 の証明（完全 prism 上の根の割り算包で根付き拡大を直接作る、André を使わない経路）は**削除しない**。
  別名の定理として `Semiperfectoid/RootEnvelope/` に残す。その構成に使う 32 本も同じ場所へ移す。
- 新しい sorry・axiom・文献入力を加えない。B4 の公理は標準三公理のまま（André の補題 Thm 7.14 は証明済み）。

## 1. 作業 A：移動（スクリプト）

移動先は [bhatt-scholze-codex-w3-moves.json](../../../evidence/bhatt-scholze/bhatt-scholze-codex-w3-moves.json)（33 本）。

| 移動先 | 本数 | 中身 |
| --- | --- | --- |
| `Semiperfectoid/AndreSurjectivity`（改名） | 1 | 旧 `RootedExtension/AndreSurjectivityConditional`。André 経由の全射性 `surjective_of_isPerfectoidization_of_andre` |
| `Semiperfectoid/RootEnvelope/` | 14 | 完全 prism 上の根の割り算包（\(X^p-b\) 族の prismatic envelope）の離散性・p 完全忠実平坦性・perfectoid 候補、根付き拡大 `exists_rootedPerfectoidExtension_of_perfectPrism`、rank 1 の元の根列、根付き生成族からの降下 |
| `Semiperfectoid/RootEnvelope/Source/` | 11 | 割り算包の源の構成と、完備化・H⁰ の比較 |
| `Semiperfectoid/RootEnvelope/BoundedSupport/` | 7 | 任意の元族を有界台の余極限で扱う部分 |

```bash
set -o pipefail
git status --short SerrePositivity/BhattScholze SerrePositivity/CLMST    # 空であること
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w3-moves.json
# 期待値（2026-10-25 12:30、W2 後の main で確認）："moves": 33, "stubs": 0, "owned_files_rewritten": 38, "foreign_imports_without_stub": []
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w3-moves.json --apply
```

件数が違う場合は `--apply` せずに報告する。移動するファイルを import している移動外のファイルは 6 本あるが、どれもどこからも使われない旧経路のもので、
スクリプトが import 行を書き換える。

## 2. 作業 B：証明の差し替え（手作業、移動の後）

以下のパスは移動後のもの。

### B1. 旧い証明を別名の定理として残す

新規ファイル `SerrePositivity/BhattScholze/Semiperfectoid/RootEnvelope/RootEnvelopeSurjectivity.lean` を作る。

- 先頭は他の BS ファイルと同じ形（`module`、`public import`、`@[expose] public noncomputable section`、`universe u`、
  `set_option backward.isDefEq.respectTransparency false`、`set_option backward.defeqAttrib.useBackward true`、
  `namespace SerrePositivity.BhattScholze`、`variable {p : ℕ} [Fact p.Prime] {R S C : Type u}`、`variable [CommRing R] [CommRing S] [CommRing C]`）。
- import は次の 2 本：
  `SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.PerfectPrismRootedPerfectoidExtension`、
  `SerrePositivity.BhattScholze.Semiperfectoid.SemiperfectoidPerfectoidization`。
- 定理 `surjective_of_isPerfectoidization_of_semiperfectoid_quotient_of_rootEnvelope` を置く。型は B4 の
  `surjective_of_isPerfectoidization_of_semiperfectoid_quotient` と**同じ**（仮定 `hR q hq hS f hf`）で、証明は
  現在の `Semiperfectoid/SemiperfectoidSurjectivity.lean` の同定理の証明（`rcases hR with …` から最後の `exact …` まで）を**そのまま**写す。
- docstring（概要／方針／規約／使われ方）：
  - 概要：perfectoid 環の導来 p 完備な全射商の任意の perfectoid 化は全射（Thm 7.4）の、André の補題を使わない別証明。
  - 方針：完全 prism 上で核の元に両立する p 冪根を添加する割り算包を作り、その完備化が p 完全忠実平坦な perfectoid 拡大になることを示して降下する。
  - 規約：主張は B4 と同じ。B4 本体は原典どおり André 経由（`Semiperfectoid/SemiperfectoidSurjectivity`）。
  - 使われ方：主定理の経路では使わない。完全 prism 上の \(X^p-b\) 族の prismatic envelope の計算（A3 の候補）とともに保存する。

### B2. B4 本体を André 経由にする

`SerrePositivity/BhattScholze/Semiperfectoid/SemiperfectoidSurjectivity.lean`：

- 1 本目の import `…Semiperfectoid.RootedExtension.PerfectPrismRootedPerfectoidExtension`（移動後は `…RootEnvelope.…`）を
  `public import SerrePositivity.BhattScholze.Semiperfectoid.AndreSurjectivity` に替える。他の import は残す。
- `surjective_of_isPerfectoidization_of_semiperfectoid_quotient` の証明を次に替える（型は変えない）：
  ```lean
    surjective_of_isPerfectoidization_of_andre R S C p hR q hq hS f hf
  ```
  （`:= by` を外して項にするか、`by exact …` にする。どちらでもよい）
- `exists_surjective_perfectoidization_of_semiperfectoid_quotient`・`surjective_of_isPerfectoidization_of_adic_complete_quotient` は変えない。
- module docstring を「概要／方針／規約／使われ方」の形に書き直す：
  - 概要：BS 著者版 Thm 7.4。perfectoid 環 R の導来 p 完備な全射商 S の任意の perfectoid 化は全射。
  - 方針：原典どおり、André の補題（Thm 7.14、証明済み）で絶対整閉な perfectoid 環 T へ p 完全忠実平坦に拡大し、
    T では核の全元が両立する p 冪根を持つので全射性が出て、それを R へ降下する（`Semiperfectoid/AndreSurjectivity`）。
  - 規約：p ねじれなし・有限性・古典的完備性は仮定しない。André を使わない別証明は `Semiperfectoid/RootEnvelope/RootEnvelopeSurjectivity`。
  - 使われ方：CLMST、`Almost/PerfectoidIdealLemma103`、`Perfectoidization/Prop813PerfectoidBaseChange`、`Semiperfectoid/PerfectoidizationSurjectiveMap`、`Inputs/SemiperfectoidSurjectivity`。
- 定理の docstring の一文目は今のまま（主張）でよい。「証明は André の補題経由」と一文足す。

### B3. André 経由版の docstring を直す

`SerrePositivity/BhattScholze/Semiperfectoid/AndreSurjectivity.lean`：コードは変えない。module docstring と定理 docstring の
「既存André入力に相対的」「sorryAx に依存」「B4の引用解消ではない」という記述を削り、
「André の補題（Thm 7.14、`Inputs.exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed`、証明済み）による、原典の Thm 7.4 の証明」と書く。

### B4. 参照の文言

`SerrePositivity/BhattScholze/Inputs/AndreFlatness.lean:35` の docstring 中の `AndreSurjectivityConditional` を `AndreSurjectivity` に直す（文言のみ）。

## 3. 禁止事項

- B4 の公開定理 3 本の名前・型の変更。`surjective_of_isPerfectoidization_of_andre` の名前・型の変更。
- 移動するファイル（33 本）の中身の変更。B1〜B4 に書いた以外のコードの変更。
- 所有範囲外のファイルの変更（`SerrePositivity.lean`、`CommutativeAlgebra/`、`scripts/refactor/` を含む）。

## 4. 受入条件

BS-W1 §5「作業 3 の後」と同じコマンド一式（BS・CLMST の全モジュールのビルド、全 BS・CLMST 監査、`audit_f5`・`audit_f7`、
`scripts/audit_andre_*.lean`、構造監査、CommutativeAlgebra の 4 モジュール）を実行し、すべてエラーなし・終了 0。
ログの全体を `grep -nE "^error|error:|sorryAx"` で確かめてから報告する（宣言名に含まれる `error` は除いてよい）。加えて：

```bash
# 新しいファイルも含めてビルド
lake build SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.RootEnvelopeSurjectivity 2>&1 | tail -2
# B4 と別証明の公理（どちらも標準三公理のみであること）
cat > /tmp/bs_w3_axioms.lean <<'EOF'
import SerrePositivity.BhattScholze.Semiperfectoid.SemiperfectoidSurjectivity
import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.RootEnvelopeSurjectivity
#print axioms SerrePositivity.BhattScholze.surjective_of_isPerfectoidization_of_semiperfectoid_quotient
#print axioms SerrePositivity.BhattScholze.surjective_of_isPerfectoidization_of_semiperfectoid_quotient_of_rootEnvelope
EOF
lake env lean /tmp/bs_w3_axioms.lean
# B4 本体が RootEnvelope を import していないこと（出力が空）
grep -n "RootEnvelope" SerrePositivity/BhattScholze/Semiperfectoid/SemiperfectoidSurjectivity.lean
```

## 5. コミット

作業 A と作業 B を別コミットにする。

```bash
set -o pipefail
git commit --only SerrePositivity/BhattScholze SerrePositivity/CLMST SerrePositivity/Inputs/Perfectoidization.lean \
  scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit_andre_*.lean \
  scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean -m "$(cat <<'EOF'
refactor(bs): move the B4-only root-envelope construction to Semiperfectoid/RootEnvelope/

Move the 32 modules used only by the André-free proof of BS Thm 7.4 (prismatic envelopes of
X^p - b families over a perfect prism, their discreteness and flatness, the rooted perfectoid
extension) to Semiperfectoid/RootEnvelope/ with Source/ and BoundedSupport/, and rename
RootedExtension/AndreSurjectivityConditional to Semiperfectoid/AndreSurjectivity. Plan:
formalization-plans/bhatt-scholze-codex-w3-moves.json. Only import lines change.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
git add SerrePositivity/BhattScholze/Semiperfectoid/RootEnvelope/RootEnvelopeSurjectivity.lean
git commit --only SerrePositivity/BhattScholze/Semiperfectoid/SemiperfectoidSurjectivity.lean \
  SerrePositivity/BhattScholze/Semiperfectoid/AndreSurjectivity.lean \
  SerrePositivity/BhattScholze/Semiperfectoid/RootEnvelope/RootEnvelopeSurjectivity.lean \
  SerrePositivity/BhattScholze/Inputs/AndreFlatness.lean -m "$(cat <<'EOF'
refactor(bs): prove BS Thm 7.4 through André's lemma as in the paper

The public B4 theorem keeps its name and type and is now proved by
surjective_of_isPerfectoidization_of_andre (André's lemma, Thm 7.14, then descent along a
p-completely faithfully flat map to an absolutely integrally closed perfectoid ring). The
previous André-free proof is kept verbatim as
surjective_of_isPerfectoidization_of_semiperfectoid_quotient_of_rootEnvelope.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
```

## 6. 報告してほしいこと

二つのコミットハッシュ、dry-run の出力、ビルドのジョブ数・所要時間・grep の結果、二つの定理の `#print axioms`、想定と違ったこと。
失敗したときは直さずにエラーをそのまま報告する。
