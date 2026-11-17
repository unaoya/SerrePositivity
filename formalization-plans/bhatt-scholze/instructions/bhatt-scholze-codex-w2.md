# Codex 作業指示書 BS-W2：BhattScholze/ を原典の節ごとに再配置する

作成：2026-10-25（BS 作業チャット）。宛先：Codex。**BS-W1 の作業 3b のコミットが済んでから始める。**
宣言の名前・名前空間・型・証明は変えない。変えるのはモジュールの場所と import 行だけ。

## 0. 前提

BS-W1 の §0 と同じ（所有範囲、他レーンの並行作業、root ビルドの禁止、`git add -A`・`git commit -a` の禁止）。
所有範囲に BS 専用の監査 `scripts/audit_andre_*.lean` を加える（スクリプトの書き換え対象に含めた）。

## 1. 新しい配置

W1 の分割（主題別）を、原典（著者版）の節ごとに組み直す。合計 760 本を移す。移動先は
[bhatt-scholze-codex-w2-moves.json](../../../evidence/bhatt-scholze/bhatt-scholze-codex-w2-moves.json)。ファイル名は変えない。
「経路」列は、主定理の経路（CLMST などの利用先と `Inputs/` からの import 閉包）に入る本数。

| ディレクトリ | 本数 | 経路 | 中身（原典） |
| --- | --- | --- | --- |
| `Delta/Basic/` | 20 | 16 | §2.1：定義（W₂ 切断）、Frobenius 持ち上げ、商と δ 閉包、余極限・Witt への写像 |
| `Delta/Extension/` | 14 | 12 | §2.2：局所化、I 進完備化、導来 (p,d) 完備化の H⁰ への延長（Lemma 2.18 の形） |
| `Delta/Distinguished/` | 2 | 2 | §2.3：Lemma 2.23〜2.25、Ex 2.20(1) |
| `Delta/Perfect/` | 13 | 13 | §2.4：完全化、Lemma 2.28、Cor 2.31、Lemma 2.32〜2.34 |
| `Delta/Free/` | 20 | 12 | Lemma 2.11（自由 δ 環と Frobenius）、相対自由 δ 環、多項式の δ 構造 |
| `Delta/Free/Finite/` | 25 | 13 | B4 用：有限段での δ の反復と Witt 座標の計算 |
| `Delta/Division/` | 14 | 3 | δ 除算 A{a_s/d} の構成と一般的な性質（Lemma 2.36・Prop 3.13・Cor 7.3 で使う形） |
| `Delta/Division/Relations/` | 45 | 34 | B4 用：関係式・Witt 正規化・評価源・係数の商と Tor |
| `Delta/DividedPower/` | 74 | 0 | §2.5：pd 包との関係（Lemma 2.35・2.36、主・rank 1 の pd 包）。Rem 7.15 用 50、未使用 24。**移動なし** |
| `Prism/Basic/` | 9 | 4 | §3：Def 3.2、Lemma 3.1・3.5（剛性）、Ex 3.3、向き付き prism |
| `Prism/Perfection/` | 25 | 14 | §3：Lemma 3.9（prism の完全化）、p 進完備 δ 完全化、完全 δ 環の PD 完備化 prism |
| `Prism/Perfectoid/` | 28 | 26 | §3：Thm 3.10（完全 prism ↔ perfectoid 環）、Witt 商・Fontaine 写像・tilt |
| `Prism/Tensor/` | 15 | 12 | 完全 δ 環・完全 prism の完備テンソル（Lemma 10.3 と Prop 8.13 の入力） |
| `Prism/Residue/` | 11 | 11 | prism 係数の冪商・mod p 還元・導来底変換の一般補題 |
| `Perfectoidization/` | 17 | 12 | §8 の環版：perfectoid 化の普遍性・完備テンソル・底変換、Prop 8.13 環版、Cor 8.12 の環版 excision |
| `Perfectoidization/WittPresentation/` | 7 | 6 | Witt 商表示を持つ環のテンソルの perfectoid 化 |
| `Semiperfectoid/` | 8 | 7 | §7.1：Cor 7.3（B3）、Thm 7.4（B4）の結論と全射性の移送 |
| `Semiperfectoid/RootedExtension/` | 36 | 27 | Thm 7.4 の別証明の根付き拡大（W1 の `RootedExtension/` をそのまま下へ） |
| `Semiperfectoid/RootedExtension/{DeltaRoot,Division,CompatibleRoot,DeltaAlgebra}/` | 97・94・16・16 | 57・46・13・16 | 同上の下位構成（W1 と同じ分け方） |
| `Almost/` | 10 | 7 | §10：Lemma 10.3、Prop 10.2、Rem 10.7、almost な核・余核 |
| `Andre/` | 46 | 46 | §7.3：Thm 7.14 の本証明の一元拡大（直下）。**移動なし** |
| `Andre/Transfinite/` | 30 | 26 | Thm 7.14 の ω₁ 反復。**移動なし** |
| `Andre/Remark715/` | 163 | 0 | Rem 7.15 の pd 包計算との照合（主定理に不要）。`PowerRoot*`、`PerfectPrismVarpi*` など |
| `Andre/Remark715/{Unconditional,VarpiComparison,Unoriented}/` | 48・9・4 | 0 | 同上（W1 までの `Andre/` のサブディレクトリを下へ） |
| `Andre/Variants/` | 42 | 0 | Thm 7.14 の一般化版（任意族・一般基底、E1・E2）。root の集約だけが import |
| `PerfectoidizationInterface/`、`Inputs/` | 11・5 | 11・4 | 界面と文献入力。**移動なし**（EInfinity が `PerfectoidizationInterface.Interface` を import） |
| 直下 | 34 | — | 入口 `Perfectoidization.lean`・`PerfectoidizationInterface.lean` と、W1 の転送スタブ 32 本 |

ディレクトリ単位の依存は Delta → Prism → Perfectoidization → Semiperfectoid → Almost → Andre の順に並ぶ（`Inputs` への依存を除く）。
逆向きは `Perfectoidization/Prop813PerfectoidBaseChange → Semiperfectoid/SemiperfectoidSurjectivity` の一本だけ
（Prop 8.13 環版の商への入口が B4 の全射性を使う）。モジュール単位の循環はない。

### 外から import されるモジュール

root の `SerrePositivity.lean` が旧名で import している `Andre.MonicRootedExtension` と `Andre.Unoriented` の 2 本は、
W1 と同じく旧名の位置に転送スタブを置く（JSON の `stubs`）。KST が import する `Andre.MonicRelationRegularSequence` と、
EInfinity が import する `PerfectoidizationInterface.Interface` は動かさない。

## 2. 実行

```bash
set -o pipefail
git status --short SerrePositivity/BhattScholze SerrePositivity/CLMST    # 空であること（W1 がコミット済み）
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w2-moves.json
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w2-moves.json --apply
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w2-moves.json --stubs   # "wrote 2 stubs"
```

dry-run の期待値（2026-10-25 12:40、W1 の移動を適用した作業ツリーで確認）：

```text
"moves": 760, "stubs": 2, "owned_files_rewritten": 803, "foreign_imports_without_stub": []
```

件数が違う場合は `--apply` せずに報告する。
`scripts/audit/bhatt_scholze.lean`・`scripts/audit/clmst.lean` では、import 行に加えて `let mods` の名前一覧もスクリプトが書き換える
（W1 で一覧が旧名のまま残り監査が失敗したため、10-25 に追加）。この二ファイルに限り、import 行以外の差分を許す。
さらに、所有範囲の Lean ファイルでバッククォートの直後にあるモジュール名（André の監査 `Audit.lean`・`scripts/audit_andre_*.lean` の
`let modules` の一覧、W1 のスタブの docstring）も置き換える。W2 の初回の全体ビルドで、André の監査 4 本が旧名の一覧のために失敗した（10-25）。
`--apply` の後に気づいた場合は、§3 の前に次の単独の置き換えを行う（期待値：31 ファイル・41 件）。

```bash
python3 - <<'PY'
import json, re, subprocess, os
mv = json.load(open('evidence/bhatt-scholze/bhatt-scholze-codex-w2-moves.json'))['moves']
bt = re.compile(r"(?<=`)SerrePositivity\.BhattScholze\.[\w.']+")
own = [r"^SerrePositivity/BhattScholze/.*\.lean$", r"^SerrePositivity/CLMST/.*\.lean$", r"^scripts/audit_andre_[^/]*\.lean$",
       r"^scripts/audit_bhatt_scholze[^/]*\.lean$", r"^scripts/audit_clmst[^/]*\.lean$"]
files = [f for f in subprocess.check_output(['git', 'ls-files', '--cached', '--others', '--exclude-standard']).decode().split('\n')
         if f and os.path.isfile(f) and any(re.match(r, f) for r in own)]
nf = n = 0
for f in files:
    s = open(f).read()
    k = sum(1 for t in bt.findall(s) if t in mv)
    if k:
        open(f, 'w').write(bt.sub(lambda m: mv.get(m.group(0), m.group(0)), s)); nf += 1; n += k
print('files', nf, 'replacements', n)
PY
```

## 3. 受入条件

BS-W1 §5 の「作業 3 の後」と同じコマンド一式に、`scripts/audit_andre_*.lean` の二本を加えて実行し、すべてエラーなし・終了 0。
加えて次を確認する。

```bash
git diff --cached -M --diff-filter=RM -- SerrePositivity scripts \
    ':!scripts/audit/bhatt_scholze.lean' ':!scripts/audit/clmst.lean' ':!**/Audit.lean' ':!**/UnconditionalAudit.lean' ':!scripts/audit_andre_*.lean' \
  | grep -E '^[-+]' | grep -vE '^(\+\+\+|---) ' \
  | grep -vE '^[-+][ \t]*(public )?import '    # 出力が空（生成監査の名前一覧は除く）
ls SerrePositivity/BhattScholze/Delta/*.lean SerrePositivity/BhattScholze/Prism/*.lean 2>/dev/null | wc -l   # 0
```

## 4. コミット

W1 と同じく、移動（4a）とスタブ（4b）を分ける。4a の前に 2 本のスタブを削除し、4a のあと `--stubs` で作り直して 4b にする。

```bash
set -o pipefail
rm SerrePositivity/BhattScholze/Andre/MonicRootedExtension.lean SerrePositivity/BhattScholze/Andre/Unoriented.lean
git commit --only SerrePositivity/BhattScholze SerrePositivity/CLMST SerrePositivity/Inputs/Perfectoidization.lean \
  scripts/audit_bhatt_scholze*.lean scripts/audit_clmst*.lean scripts/audit_andre_*.lean \
  scripts/audit/bhatt_scholze.lean scripts/audit/clmst.lean -m "$(cat <<'EOF'
refactor(bs): arrange BhattScholze/ by the sections of the paper

Move 760 modules following evidence/bhatt-scholze/bhatt-scholze-codex-w2-moves.json: Delta/ by
sections 2.1-2.4 (with Free/Finite/ and Division/Relations/ for B4-only computations), Prism/
by Lemma 3.9 and Thm 3.10, Perfectoidization/ (§8 ring version), Semiperfectoid/ (§7.1, with
the B4 RootedExtension/), Almost/ (§10), and Andre/ split into the Thm 7.14 proof, Remark715/
and Variants/. Only import lines change; declaration names and namespaces are unchanged.

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
git show --stat -M HEAD | tail -2
python3 evidence/bhatt-scholze/bhatt-scholze-move-modules.py evidence/bhatt-scholze/bhatt-scholze-codex-w2-moves.json --stubs
git add SerrePositivity/BhattScholze/Andre/MonicRootedExtension.lean SerrePositivity/BhattScholze/Andre/Unoriented.lean
git commit --only SerrePositivity/BhattScholze/Andre/MonicRootedExtension.lean SerrePositivity/BhattScholze/Andre/Unoriented.lean -m "$(cat <<'EOF'
refactor(bs): keep forwarding stubs for two Andre modules imported by the root

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
EOF
)"
```

## 5. 報告してほしいこと

二つのコミットハッシュ、dry-run の出力、受入条件の各コマンドの出力末尾、ビルドのジョブ数と所要時間。
失敗したときは直さずにエラーをそのまま報告する。
