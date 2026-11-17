# Codex 作業指示書 BS-W1：監査 838 行の修正、Q10 の適用、BhattScholze/ 直下の主題別分割

作成：2026-10-25（BS 作業チャット）。宛先：Codex。勉強ノート第 0 章の BR1〜BR3（`exposition/ja/bs/00-map.html` §7）。
三つとも公開されている宣言の名前・型・数学の主張は変えない。作業 3 はモジュール（ファイル）の場所だけを変える。
**作業 1 → 2 → 3 の順に行い、作業ごとにコミットする（作業 3 は 3a・3b の二つ）。**

## 0. 前提

- 作業ディレクトリ：リポジトリ root。ブランチ：`main`。
- ∞ 圏基盤の 8 レーンが `InfinityCategories/`・`KST/`・`DifferentialGraded/`・`EInfinity/` を同時に編集・ビルドしている。
  git status に見える他レーンの未コミット変更には触らない・stage しない。**root の `lake build SerrePositivity` は実行しない。**
- 所有範囲（編集してよい）：`SerrePositivity/BhattScholze/`、`SerrePositivity/CLMST/`、`SerrePositivity/Inputs/Perfectoidization.lean`、
  `scripts/audit_bhatt_scholze*`、`scripts/audit_clmst*`、`scripts/audit/bhatt_scholze.lean`、`scripts/audit/clmst.lean`、
  `formalization-plans/bhatt-scholze*`。これ以外は読むだけ。

## 1. 作業 1（BR3）：`scripts/audit_bhatt_scholze_refactoring.lean:838` の型不一致

症状（2026-10-25 09:15 に再現）：

```text
scripts/audit_bhatt_scholze_refactoring.lean:838:41: error: Application type mismatch: The argument
  Ideal.Quotient.mk (Ideal.span {↑p, MvPolynomial.C (MvPolynomial.C d)})
has type
  @RingHom (MvPolynomial (σ × ℕ) P) (... ⧸ ...) AddMonoidAlgebra.ring.toNonAssocSemiring ...
but is expected to have type
  @RingHom (RelativeFreeDeltaRing σ) ?m.157 AddMonoidAlgebra.nonAssocSemiring ...
```

838 行は section `BoundedSupportTor` の `example` の結論。結論の前の `let := deltaDivisionSourceEvaluationAlgebra E r` のあとで、
`I` の台が abbrev `RelativeFreeDeltaRing` を開いた `MvPolynomial (σ × ℕ) P` として推論される。

**変更**：同ファイル 829〜830 行の局所記法を次に置き換える（この一箇所だけ）。

```lean
local notation "ψ" => RingHom.comp (Ideal.Quotient.mk (R := L) I)
  (deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d))
```

一時コピーでの試験では、これだけで監査全体が終了 0 になった。

**禁止**：`example` の削除・`sorry` 化・型の弱化、`exact` の右辺の変更、
ソース `SerrePositivity/BhattScholze/DeltaDivisionBoundedSupportTor.lean` の変更。

## 2. 作業 2（BR2＝Q10）：普遍性の手書き展開を既存補題に置換

既存の共通補題（変更しない）：

```lean
-- SerrePositivity/CommutativeAlgebra/PerfectoidizationFunctor.lean:30
theorem SerrePositivity.IsPerfectoidization.precomp_ringEquiv
    (hf : IsPerfectoidization p f) (e : T ≃+* S) :
    IsPerfectoidization p (f.comp e.toRingHom)
```

| ファイル | 置き換える `have` | 置き換え後 |
| --- | --- | --- |
| `SerrePositivity/BhattScholze/RootedKernelSurjectivity.lean` | `have hfe : IsPerfectoidization p (f.comp e.toRingHom) := by refine ⟨hf.1, ?_⟩ …`（約 20 行） | `have hfe : IsPerfectoidization p (f.comp e.toRingHom) := hf.precomp_ringEquiv e` |
| `SerrePositivity/BhattScholze/RootedPresentationSurjectivity.lean` | 同上 | 同上 |
| `SerrePositivity/BhattScholze/RootedIdealSurjectivity.lean` | `have hff : IsPerfectoidization p ff := by refine ⟨hf.1, ?_⟩ …` | `have hff : IsPerfectoidization p ff := hf.precomp_ringEquiv e.symm` |

`let e`・`let ff` とその後の議論は残す。新しい import は不要（三ファイルの import 閉包から補題が見える）。
置換後の三ファイルを一時コピーで `lake env lean` にかけ、エラーなしを確認済み（2026-10-25 09:30）。

**禁止**：三定理と `compatibleRootFamilyZeroIdeal_eq_of_roots_on_ideal` の名前・型・仮定・docstring の変更。
`CommutativeAlgebra/` の変更、新しい補題の追加。

## 3. 作業 3（BR1）：BhattScholze/ 直下 618 ファイルの主題別分割

### 3.1 新しい配置

直下の 618 モジュールのうち 616 本を次のディレクトリへ移す。ファイル名（モジュール名の最後の部分）は変えない。
`Andre/`・`Inputs/`・`PerfectoidizationInterface/` は動かさない。入口の `Perfectoidization.lean`・`PerfectoidizationInterface.lean` も直下に残す。

| ディレクトリ | 本数 | 内容（原典） |
| --- | --- | --- |
| `Delta/` | 55 | δ 構造の定義と基本（§2.1〜2.4：W₂ 切断、商・局所化・完備化、distinguished、完全 δ 環、Witt） |
| `Delta/Free/` | 42 | 自由 δ 環・相対自由 δ 環・多項式の δ 構造（Lemma 2.11） |
| `Delta/Division/` | 57 | δ 環での除算 A{f/d} の一般構成と Witt 関係式 |
| `Delta/DividedPower/` | 74 | pd 包との関係（§2.5：Lemma 2.35・2.36、主 pd 表示、rank 1 の pd 包） |
| `Prism/` | 97 | prism、完全 prism と perfectoid 環（§3、Thm 3.10）、Fontaine 写像、完全 δ 環のテンソル |
| `Perfectoidization/` | 24 | 環の perfectoid 化の普遍性、完備テンソル、B3（Cor 7.3）、Lemma 10.3、excision の環版 |
| `RootedExtension/` | 32 | B4 の根付き拡大の残り（モニック族、Rooted*Surjectivity、André 条件付き版ほか） |
| `RootedExtension/DeltaRoot/` | 97 | 根の変数の割り算包の源（DeltaRoot*） |
| `RootedExtension/Division/` | 94 | B4 で使う割り算包の有限段・Koszul・Tor 計算（DeltaDivision*・DeltaPDivision* のうち根付き拡大用） |
| `RootedExtension/CompatibleRoot/` | 16 | 両立する根の族と商（CompatibleRoot*） |
| `RootedExtension/DeltaAlgebra/` | 16 | δ 代数の完全化段（DeltaAlgebra*・PerfectPrismDeltaAlgebra*） |
| `Results/` | 12 | 根付き拡大を使う結論：B4（Thm 7.4）、B5（Prop 10.2・Rem 10.7）、Prop 8.13 の底変換 |

各モジュールの移動先は [bhatt-scholze-codex-w1-moves.json](../../../evidence/bhatt-scholze/bhatt-scholze-codex-w1-moves.json) の `moves`。
分類は名前の規則で種を置いたうえで、import 関係に合わせて調整した（ディレクトリ単位の逆向き import は 15 本残る。モジュール単位の循環はない）。

### 3.2 外から import されているモジュール：転送スタブ

所有範囲外の次のファイルが、移すモジュールのうち 32 本を旧名で import している。これらのファイルは**変更しない**。

- root の `SerrePositivity.lean`（26 本）
- `CommutativeAlgebra/` の `AbsolutelyIntegrallyClosedPerfectoidQuotient`・`PerfectoidIdeal`・`PerfectoidIdealCompatibleRoots`・`PerfectoidIdealCover`
- `scripts/audit_f5.lean`、`scripts/audit_f7.lean`

32 本は旧名の位置に、新しい名前を `public import` するだけの転送モジュール（宣言なし、docstring 付き）を置く。一覧は JSON の `stubs`。

### 3.3 実行

`scripts/move_module.py` は使わない（リポジトリ全体の `.lean` を書き換えるため）。書き換えを所有範囲に限った一回限りのスクリプト
[bhatt-scholze-codex-w1-apply.py](../../../evidence/bhatt-scholze/bhatt-scholze-codex-w1-apply.py) を使う。既定は dry-run。`--apply` で `git mv` と import の書き換え、`--stubs` でスタブの作成を行う。
スタブを移動と同じコミットに入れると、旧パスが「変更」扱いになって git が rename を検出できないので、コミットは 3a（移動）と 3b（スタブ）に分ける。
スクリプトはコミット・ビルドをしない。dry-run の期待値（2026-10-25 10:20、作業 1・2 の前の状態で確認）：

```text
"moves": 616, "stubs": 32, "owned_files_rewritten": 708, "foreign_imports_without_stub": []
```

手順：

```bash
set -o pipefail
git status --short SerrePositivity/BhattScholze SerrePositivity/CLMST   # 作業 1・2 のコミット後、空であること
python3 evidence/bhatt-scholze/bhatt-scholze-codex-w1-apply.py            # dry-run。上の期待値と一致すること
python3 evidence/bhatt-scholze/bhatt-scholze-codex-w1-apply.py --apply
python3 evidence/bhatt-scholze/bhatt-scholze-codex-w1-apply.py --stubs    # "wrote 32 stubs"
```

ビルドと監査（§5）はスタブを置いた状態で行い、通ってから 3a・3b の順にコミットする（§6）。

### 3.4 禁止

- 宣言名・名前空間・型・証明の変更（import 行以外の差分が出てはいけない。スタブは新規ファイル）。
- 所有範囲外のファイルの変更（`SerrePositivity.lean`、`CommutativeAlgebra/`、`scripts/audit_f5.lean`・`audit_f7.lean`、`scripts/refactor/` を含む）。
- 分類の変更。ビルドが通らない移動があれば、移動を戻さずに報告する。

## 4. 全体の禁止事項

- 新しい `sorry`・`axiom`・文献入力を加えない。
- root の `lake build SerrePositivity` を実行しない。`git add -A`・`git commit -a` を使わない。

## 5. 受入条件

作業 1・2 の後：

```bash
set -o pipefail
lake build SerrePositivity.BhattScholze.RootedKernelSurjectivity \
  SerrePositivity.BhattScholze.RootedPresentationSurjectivity \
  SerrePositivity.BhattScholze.RootedIdealSurjectivity \
  SerrePositivity.BhattScholze.RootedFamilyPerfectoidSurjectivityDescent \
  SerrePositivity.BhattScholze.RootedTensorBaseChangeSurjectivity \
  SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedPerfectoidQuotient 2>&1 | tail -5
lake env lean scripts/audit_bhatt_scholze_b4.lean 2>&1 | grep -E "error|sorryAx"; echo "b4 exit=${PIPESTATUS[0]}"
lake env lean scripts/audit_bhatt_scholze_refactoring.lean 2>&1 | grep -E "error|sorryAx"; echo "refactoring exit=${PIPESTATUS[0]}"
```

作業 3 の後（BS と CLMST の全モジュールをビルドする。時間がかかる）：

```bash
set -o pipefail
{ find SerrePositivity/BhattScholze SerrePositivity/CLMST -name '*.lean'; echo SerrePositivity/Inputs/Perfectoidization.lean; } \
  | sed -e 's|\.lean$||' -e 's|/|.|g' | sort > /tmp/bs_w1_targets.txt
wc -l /tmp/bs_w1_targets.txt
xargs lake build < /tmp/bs_w1_targets.txt 2>&1 | tail -5
for a in scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean \
         scripts/audit_f5.lean scripts/audit_f7.lean; do
  lake env lean "$a" > /tmp/out.txt 2>&1; echo "$a exit=$? $(grep -cE 'error' /tmp/out.txt) errors"
done
python3 scripts/audit_bhatt_scholze_structure.py; echo "structure exit=$?"
lake build SerrePositivity.CommutativeAlgebra.PerfectoidIdeal SerrePositivity.CommutativeAlgebra.PerfectoidIdealCover \
  SerrePositivity.CommutativeAlgebra.PerfectoidIdealCompatibleRoots \
  SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosedPerfectoidQuotient 2>&1 | tail -3
```

- ビルドが成功し、全監査がエラーなし・終了 0。`audit_bhatt_scholze_andre_conditional` など sorryAx を表示する監査は、表示が作業前と同じであること。
- `git diff --cached -M --stat` で、移動が 616 本の rename（類似度の閾値は設けない。短いファイルでは import 行だけの変更でも 80% 前後になる。10-25 に 90% 以上の条件を撤回）、変更が import 行だけであること（スタブはこの時点で未追跡）。
  確認例：`git diff --cached -M --diff-filter=RM -- SerrePositivity scripts | grep -E '^[-+]' | grep -vE '^(\+\+\+|---) ' | grep -vE '^[-+][ \t]*(public )?import '`
  の出力が空（rename と変更のうち import 行以外の差分がない）。スタブは `git diff --cached --diff-filter=A --stat` で 32 本。
- 作業 1・2 は docstring を変えない。作業 3 のスタブには上の docstring を付ける（スクリプトが書く）。

## 6. コミット

所有範囲のパスだけを指定して `--only` でコミットする。帰属行は `Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`。

```bash
set -o pipefail
git commit --only scripts/audit_bhatt_scholze_refactoring.lean -m "$(cat <<'EOF'
fix(bs-audit): pin the ring of the quotient map in the bounded-support Tor audit

The `ψ` notation in section BoundedSupportTor elaborated `Ideal.Quotient.mk I` over the unfolded
`MvPolynomial (σ × ℕ) P` after the statement-level `let`, mismatching `RelativeFreeDeltaRing`.
Pass `(R := L)` explicitly. The example and the audited theorem are unchanged.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
git commit --only SerrePositivity/BhattScholze/RootedKernelSurjectivity.lean \
  SerrePositivity/BhattScholze/RootedPresentationSurjectivity.lean \
  SerrePositivity/BhattScholze/RootedIdealSurjectivity.lean -m "$(cat <<'EOF'
refactor(bs): use IsPerfectoidization.precomp_ringEquiv in the rooted surjectivity proofs (Q10)

Replace three hand-unfolded proofs that a perfectoidization stays universal after precomposing
with a ring isomorphism by the existing common lemma. Public names and types are unchanged.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
# 作業 3a：移動と import の書き換え。旧パスは HEAD で追跡されているため、スタブが作業ツリーにあると
# `git commit --only <dir>` がそれを「変更」として取り込み rename が壊れる（Codex が一時リポジトリで確認、10-25）。
# 検証が済んだら 32 本のスタブをいったん削除してから 3a をコミットし、3b の前に --stubs で作り直す。
xargs rm -- < <(python3 -c "import json;print('\n'.join(m.replace('.','/')+'.lean' for m in json.load(open('evidence/bhatt-scholze/bhatt-scholze-codex-w1-moves.json'))['stubs']))")
git commit --only SerrePositivity/BhattScholze SerrePositivity/CLMST SerrePositivity/Inputs/Perfectoidization.lean \
  scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean -m "$(cat <<'EOF'
refactor(bs): split the flat BhattScholze/ directory by subject (BR1)

Move 616 top-level modules into Delta/ (with Free/, Division/, DividedPower/), Prism/,
Perfectoidization/, RootedExtension/ (with DeltaRoot/, Division/, CompatibleRoot/, DeltaAlgebra/)
and Results/, following formalization-plans/bhatt-scholze-codex-w1-moves.json. Only import lines
change; declaration names and namespaces are unchanged.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
git show --stat -M HEAD | tail -3      # 616 renames を確認
# 作業 3b：転送スタブ（作り直して追加する）
python3 evidence/bhatt-scholze/bhatt-scholze-codex-w1-apply.py --stubs    # "wrote 32 stubs"
python3 -c "import json;print('\n'.join(m.replace('.','/')+'.lean' for m in json.load(open('evidence/bhatt-scholze/bhatt-scholze-codex-w1-moves.json'))['stubs']))" > /tmp/bs_w1_stubs.txt
xargs git add -- < /tmp/bs_w1_stubs.txt
git commit --only $(cat /tmp/bs_w1_stubs.txt) -m "$(cat <<'EOF'
refactor(bs): keep forwarding stubs for modules imported outside the BS area

32 moved modules are imported under their old names by the root aggregator, CommutativeAlgebra
and audit_f5/f7, which this lane does not own. Each stub only re-exports the new module.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
git show --stat HEAD | tail -2         # 32 files changed（すべて新規）
```

## 7. 報告してほしいこと

- 四つのコミット（作業 1、2、3a、3b）のハッシュ、受入条件の各コマンドの出力末尾、作業 3 のビルドのジョブ数と所要時間。
- 想定と違ったこと（dot 記法の解決、dry-run の件数の違い、ビルドや監査の失敗）。失敗したときは直さずに、エラーをそのまま報告する。
