# Codex 作業指示書 IF-W0-2：整備の道具一式（R40a・R74・R64a・verify.sh の短縮）

作成：2026-10-28（∞ 基盤の整備、管理は Claude）。宛先：Codex。
計画：[infinity-foundation-plan.md](stage-i/infinity-foundation-plan.md) の段 0（R40a・R74・R64a）と §6「指示書の単位」の IF-W0-2。
**前提**：IF-W0-1（verify.sh を合否の関門にする）は main に取り込み済み（コミット `88c477612`、2026-10-28）。
**共通の前提**：[IF-W0-1](infinity-codex-w0-1.md) の §0（使い捨ての worktree、所有範囲、`git commit --only`、失敗したら止めて報告）に従う。
worktree は `../SerrePositivity-ifw0-2`、ブランチは `infra/if-w0-2`。main の作業木では作業もビルドもしない。

この指示書は大きいので、**途中に「止めて報告」の点が 2 か所ある**（§6）。

## 1. 目的

整備の本作業（W1 以降）の前に、次の道具をそろえる。どれも scripts と新しいファイルだけで、`.lean` の既存の本文は変えない。

| 部分 | 計画の番号 | 何のために使うか |
| --- | --- | --- |
| A. 層検査 | R40a | 中核の層の順序と、中核に入れてはいけないもの（KST・dg・EInfinity・モデル圏）を、import グラフで機械的に検査する。窓ごとに段階的に強制する |
| B. 対象 JSON の書式と検査 | R74 | 各窓で「どのモジュールをどこへ移すか、どう分割するか」を確定リストとして書き、実施前に検査する |
| C. 分割の道具 | R74 | `move_module.py` はモジュールの移動しかできないので、ファイルを宣言単位で分割する道具を作る |
| D. 保存検査 | R74 | 移動・分割の前後で、公開宣言の名前・型・定義の本体・公理・属性が変わっていないことを確かめる |
| E. 付け替えの補助 | R74 | 止めたレーンの未コミットのファイルの import を、移動の対応表に合わせて書き換える |
| F. 骨組み | R64a | 移し先のディレクトリと空の入口ファイルを作る |
| G. verify.sh の短縮 | （IF-W0-2 に追加） | 監査の並列実行と、結果のキャッシュ |

## 2. 所有範囲

変更・新規作成してよいもの：
- `scripts/refactor/` の下の新しいファイル。`verify.sh` と `README.md` は変更してよい。
- 新しい空の入口ファイル（§3.F の一覧のものだけ）。
- `.gitignore`（キャッシュの置き場を追加する場合）。

それ以外の `.lean` ファイル、計画文書、監査ファイル（`scripts/audit_*.lean`・`scripts/audit/*.lean`）は変更しない。
**ルートの `SerrePositivity.lean` と既存の集約ファイル（`InfinityCategories/*.lean`）にも触れない。** 新しい入口をルートに登録するのは W1（R59）で行う。

## 3. 作業

### 3.A 層検査（`scripts/refactor/layer_check.py`、設定 `scripts/refactor/layers.json`）

1. **設定ファイル `layers.json`** に次を書く。
   - **層の表**：計画 §3 の順序。下から順に次のとおり。
     ```
     Simplicial、Core（PinchedHom を含む）、Kan、Coherent、
     {F1, F1B, HomotopyLimits}（同じ層）、Stable、F2、StablePresentable、
     ModelBridge、{DGNerve, DoldKanComparison}、Derived
     ```
     各層に、対応するディレクトリの接頭辞を対応させる（例：`SerrePositivity.InfinityCategories.Core`）。まだ存在しない層（Simplicial・Kan など）も表に入れておく。
   - **中核**：Simplicial から StablePresentable まで。
   - **中核に禁止するもの**（tier ごと）：
     - tier W1：`SerrePositivity.DifferentialGraded`・`SerrePositivity.EInfinity`、および InfinityCategories の DGNerve・DoldKanComparison・Derived。
     - tier W2a：tier W1 に加えて、`SerrePositivity.KST`・`SerrePositivity.Spectra` とモデル圏のコード。
       - モデル圏のコードとは、`SerrePositivity.HomotopicalAlgebra` の `Quillen`・`HomotopyFunctionComplex`・`Generated`・`Transfer`・`Monoidal`・`Localization`・`Rectification` の各ディレクトリと、コメントを除いた本文に `ModelCategory` を含む HA のファイルのこと。
       - ただし `SerrePositivity.Spectra.PointedSimplicialSet` と `SerrePositivity.Spectra.Pointed` は、W2a で Kan/Pointed へ移すまで例外として許す。
     - tier W2b：tier W2a に加えて、中核の内部の層の順序の違反（上の層への import）。
   - **追加の規則**：Core が import してよいのは Simplicial と Mathlib だけ（いまはまだ Simplicial がないので、違反は件数として数えるだけ）。Kan は Core まで。
   - **例外の一覧**：`{from, to, 理由, 期限（窓）}` の形。最初は空にする。
2. **検査の内容**：
   - リポジトリの全 `.lean` から `import` と `public import` の行を読み、モジュールの import グラフを作る（ビルドは要らない）。
   - (1) 層をまたぐ直接の辺のうち、規則に反するものを、層の組ごとに数えて一覧にする。
   - (2) 中核の各モジュールの推移閉包に入っている禁止モジュールを、tier ごとに数える。
   - (3) 入口になっている辺（中核のモジュール → 禁止されたモジュール、の直接の辺）を一覧にする。
3. **モード**：
   - `--report`：数えて表示するだけ。
   - `--enforce TIER`：その tier の規則に違反があれば非零で終了する。
   - `--ratchet BASELINE.json`：違反の件数が基準より増えていたら非零で終了する。W1 の「違反の数を増やさない」に使う。
   - 結果は `.lake/verify/layers.json` にも書く。
4. **verify.sh との連携**：verify.sh の準備の段で `layer_check.py --report` を実行し、結果を summary.json に含める。この段は合否には数えない。強制は W1 の終わりに Claude が切り替える。

### 3.B 対象 JSON の書式と検査（`scripts/refactor/targets/README.md`、`validate_targets.py`）

1. **書式**：窓ごとに `scripts/refactor/targets/<name>.json` を置く（中身は IF-W0-3 で作る。この指示書では書式と検査の道具だけを作る）。各項目は次のとおり。
   ```json
   {"module": "SerrePositivity.X.Y",
    "action": "move | split | archive",
    "dest": "SerrePositivity.InfinityCategories.Z.Y",
    "moved": ["宣言名", ...],
    "keep": ["宣言名", ...],
    "attributes": {"宣言名": ["instance", "simp", ...]},
    "candidate": "R64",
    "note": "自由記述"}
   ```
   - `move`：モジュールをそのまま移す。`moved`・`keep` は空。
   - `split`：`moved` の宣言を `dest` へ移し、`keep` の宣言を元に残す。二つを合わせて、元のファイルの宣言をすべて覆うこと。
   - `archive`：集約から外して archive 用の場所へ移す。
2. **検査 `validate_targets.py <json>...`**：次を確かめ、問題があれば非零で終了する。
   - モジュールが存在する。同じモジュールが二つの項目に現れない。`dest` が存在しないか、骨組みのディレクトリの中にある。
   - `split` の `moved`・`keep` の名前が元のファイルに実際にあり、合わせて元のファイルの公開宣言をすべて覆う（宣言の抽出は §3.C の道具と共有する）。
   - `archive` の対象を、対象外のモジュールが import していない。
   - **移動後の層検査の試算**：JSON のとおりに移動・分割した後の import グラフを模擬的に作り、§3.A の層検査を走らせる。違反の件数が増えないこと。

### 3.C 分割の道具（`scripts/refactor/split_module.py`）

- **入力**：元のモジュール、移す宣言の名前の一覧、移し先のモジュール名。
- **動作**：
  1. 元のファイルを、トップレベルのコマンドの単位に分ける。宣言には、直前の docstring と属性（`@[...]`）を含める。
  2. 移す宣言を、元の順序のまま新しいファイルへ写す。新しいファイルの先頭には、元のファイルの見出し（`module`、import、`@[expose] public section` などの section 指定、`noncomputable section`、`set_option`、`universe`、`open`、`namespace`、`variable`）のうち必要なものを写す。名前空間の入れ子は保つ。
  3. 元のファイルから、移した宣言を除く。
  4. import を張り替える：元のファイルが移した宣言を使っていれば、新しいファイルを import する。移した宣言が元に残る宣言を使っていれば、新しいファイルが元を import する（両方向になる場合は分割できないと判定して止まる）。
  5. 元のファイルを import していたモジュールのうち、移した宣言の名前を本文で使っているものには、新しいファイルの import を加える。
- **安全策**：
  - `--dry-run` で、変更の予定（新しいファイルの中身、各ファイルの差分）を表示する。
  - 宣言の名前・本文・docstring・属性は、一文字も変えない。
  - 宣言の境界を判定できない構文（`mutual`、セクションをまたぐ `variable` の複雑な使い方など）を見つけたら、分割せずに止まる。
- **試験**：§4 の試験 C で、実際のファイル 1 本を一時的に分割し、ビルドと保存検査が通ることを確かめる（試験の後で元に戻す）。

### 3.D 保存検査（`scripts/refactor/decl_snapshot.lean` と `compare_snapshots.py`）

1. **スナップショット**：Lean のスクリプトで、指定したモジュールの集合（または名前空間の接頭辞）に含まれる公開宣言について、次を JSON に書き出す。
   - 名前、宣言の種類（def・theorem・instance・structure など）。
   - 型のハッシュ。
   - 定義の本体のハッシュ。定理以外のすべての定義（def・abbrev・instance・opaque の値を含む）が対象。定理は型だけでよい（証明の中身は変わってよい）。
   - `#print axioms` に相当する公理の集合。
   - 属性：instance（優先度を含む）、simp、reducibility（`@[reducible]` など）、`@[expose]` の有無など、取得できるもの。
   - **正規化**：private な名前は、モジュール名を含む接頭辞（`_private.<Module>.0.`）を取り除いてから比べる。補助宣言（`_proof_n`・`match_n` など）は親の宣言にまとめる。
2. **比較 `compare_snapshots.py before.json after.json [--name-map map.json]`**：
   - 名前の対応表で名前を正規化してから、各項目の一致を確かめる。
   - 消えた宣言、増えた宣言、型・本体・公理・属性の変化を一覧にして、一つでもあれば非零で終了する。
3. **試験**（§4 の試験 D）：
   - 一時的なモジュールで `def b : Bool := false` を `true` に変えたときに、本体の変化として検出されること。
   - `@[simp]` を外したときに、属性の変化として検出されること。
   - 名前空間ごと移しただけ（本文は同じ）なら差分がないこと。

### 3.E 付け替えの補助（`scripts/refactor/rebase_helper.py`）

- 移動の対応表（`move_module.py` の moves と、分割の結果の「宣言 → 新しいモジュール」の対応）を読む。
- 指定した worktree の、git で未追跡または未コミットの `.lean` ファイルについて、import の行を新しいモジュール名に書き換える。分割で宣言が移った場合は、その宣言を使っているファイルに新しい import を加える。
- `--dry-run` で差分だけを表示する。書き換えるのは import の行だけで、本文は変えない。
- これは止めたレーンが再開するときに、レーンの担当者が自分で実行するためのもの。この指示書では作るだけで、他のレーンのファイルには実行しない（試験は一時的なファイルで行う）。

### 3.F 骨組み（R64a）

次の空の入口ファイルを、リポジトリの様式（先頭の `module`、docstring に概要・方針・規約・使われ方）で作る。import はまだ書かない。docstring には、計画のどの層かと、何を置く予定かを書く。

```
SerrePositivity/InfinityCategories/Simplicial.lean
SerrePositivity/InfinityCategories/Kan.lean
SerrePositivity/InfinityCategories/Kan/Pointed.lean
SerrePositivity/InfinityCategories/ModelBridge.lean
SerrePositivity/InfinityCategories/StablePresentable.lean
SerrePositivity/InfinityCategories/Stable/Verdier.lean
SerrePositivity/InfinityCategories/Stable/Exact.lean
SerrePositivity/InfinityCategories/Stable/Infinity.lean
SerrePositivity/InfinityCategories/Stable/Lax.lean
SerrePositivity/InfinityCategories/Stable/Semiorthogonal.lean
SerrePositivity/InfinityCategories/F1B/Localization/DwyerKan.lean
SerrePositivity/InfinityCategories/F2/Filtered.lean
```

これらはどの集約ファイルにも登録しない。各ファイルが単独でビルドできること（`lake build <module>`）だけを確かめる。
§3.A の `layers.json` は、これらの接頭辞を対応する層に入れておく。

### 3.G verify.sh の短縮

1. **並列実行**：環境変数 `VERIFY_JOBS`（既定 3、1 なら従来どおり順番に実行）で監査を並列に実行する。
   - 各監査の出力・終了コード・所要時間は監査ごとに保存し、ログと要約の順序は監査名の順にそろえる。
   - 並列での実行も gate:true として扱う。
2. **結果のキャッシュ**：環境変数 `VERIFY_CACHE=1` のとき、次をすべて連結したハッシュを鍵にし、前回成功したときと鍵が同じ監査は実行せずに「キャッシュで成功」とする。
   - 監査ファイルの中身。
   - その監査が読み込むリポジトリ内の全モジュール（推移閉包）の `.olean.hash` の中身。
   - `lean-toolchain` と `lake-manifest.json` の中身。
   - verify.sh 自身の版。

   キャッシュの置き場は `.lake/verify/cache/`（追跡しない）。
   **キャッシュを使った実行は gate:false とする。** 窓の終わりの合否判定は、キャッシュなしで全部を実行する。
3. sorry 閉包の判定も、同じ鍵の考え方でキャッシュできるようにする。
4. **監査の絞り込み（試験用の入口）**：環境変数 `VERIFY_ONLY_AUDITS`（空白区切りの監査ファイル名）で、実行する監査をその一覧だけに絞れるようにする。
   - これを使った実行は gate:false とする。
   - 監査の一覧（manifest）との照合は、絞り込みと関係なく行う。
   - IF-W0-1 の故意の失敗の試験は、ビルドを飛ばしても毎回 99 本の監査を実行したので、全体で 4 時間 39 分かかった。今回の受入試験では、全体を通すのは §4 の 6 の 1 回目（`VERIFY_JOBS=3`）だけにする。それ以外の試験はこの入口で監査を数本に絞る。

## 4. 受入条件

1. **層検査**：
   - いまの HEAD で `layer_check.py --report` が動き、次を表示する。計画 §1・§4 の数値（中核の閉包に入っている外部モジュール約 1,817 本、IC → KST 175 辺など）と大きく違わないこと。違う場合は理由を報告する。
     - 層の組ごとの違反の件数。
     - tier ごとの閉包の禁止モジュールの件数。
     - 入口の辺の一覧。
   - `--enforce W1` がいまの HEAD で非零になること（まだ切断していないので、それが正しい）。
   - `--ratchet` が、件数を増やした模擬のグラフで非零、同じグラフで 0 になること。
2. **対象 JSON の検査**：
   - 小さな試験用の JSON（move 1 件・split 1 件・archive 1 件）で、正しい例は通る。誤った例（存在しない宣言、二重の登録、archive の対象に外からの利用者が残る）はそれぞれ非零になる。
3. **分割の道具（試験 C）**：
   - 計画の R72 の対象から 1 本を選び、worktree の中で末尾の Model の節を別のファイルへ分割する。候補は `HomotopicalAlgebra/Simplicial/FixedBoundaryExtensions.lean`（128 行目以降が `[ModelCategory SSet]` の節）。
   - その状態で、影響するモジュールのビルドと、§3.D の保存検査（分割の前後）が通ること。
   - 試験の後で元に戻す（コミットしない）。
4. **保存検査（試験 D）**：§3.D の 3 の三つの試験の結果が期待どおりであること。
5. **骨組み**：§3.F の 12 本が単独でビルドできること。
6. **verify.sh**：
   - `VERIFY_JOBS=3` で全体を通しで実行して PASS、gate:true になること。監査の段の所要時間を、IF-W0-1 の基準実行（3,782 秒）と比べて報告する。
   - 続けて `VERIFY_CACHE=1` で 2 回目を実行し、gate:false の PASS で、監査がすべてキャッシュで済み、短時間で終わること。
   - 監査ファイルを一つ一時的に書き換えると、その監査だけが再実行されること（試験の後で戻す）。
   - 2 回目以降の試験（キャッシュ・絞り込み・層検査の模擬など）は、`VERIFY_ONLY_AUDITS` で監査を数本に絞って行い、それぞれ数分〜十数分で終わるようにする。
7. **後片付け**：`git status` で、変更が §2 の所有範囲だけであること。一時ファイルが残っていないこと。`zsh -n`・`python3 -m py_compile` が通ること。

## 5. コミット

一つのコミットにする。

```bash
set -o pipefail
git commit --only scripts/refactor \
  SerrePositivity/InfinityCategories/Simplicial.lean SerrePositivity/InfinityCategories/Kan.lean \
  SerrePositivity/InfinityCategories/Kan/Pointed.lean SerrePositivity/InfinityCategories/ModelBridge.lean \
  SerrePositivity/InfinityCategories/StablePresentable.lean SerrePositivity/InfinityCategories/Stable/Verdier.lean \
  SerrePositivity/InfinityCategories/Stable/Exact.lean SerrePositivity/InfinityCategories/Stable/Infinity.lean \
  SerrePositivity/InfinityCategories/Stable/Lax.lean SerrePositivity/InfinityCategories/Stable/Semiorthogonal.lean \
  SerrePositivity/InfinityCategories/F1B/Localization/DwyerKan.lean SerrePositivity/InfinityCategories/F2/Filtered.lean \
  .gitignore \
  -m "$(cat <<'MSG'
chore(refactor): tooling for the infinity-foundation refactor (IF-W0-2)

- layer_check.py and layers.json: import-graph layer and closure checks (R40a)
- target JSON format and validate_targets.py (R74)
- split_module.py: split a module by declarations (R74)
- decl_snapshot.lean and compare_snapshots.py: preservation check of names,
  types, definition bodies, axioms and attributes (R74)
- rebase_helper.py: rewrite imports of paused lanes' uncommitted files (R74)
- empty entry modules for the new layers (R64a)
- verify.sh: parallel audits (VERIFY_JOBS) and a result cache (VERIFY_CACHE, non-gate)

Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>
MSG
)"
```

## 6. 止めて報告する点

1. **§3.A を作り、§4 の 1 を確かめた後**：層検査の結果を報告して止まる。
   報告に含めるもの：
   - 層の組ごとの違反の件数。
   - tier ごとの閉包の件数。
   - 入口の辺の一覧の上位 30 件。
   - 「どの層にも属さない」と判定されたモジュールの一覧（ディレクトリ単位）。

   Claude が層の表・禁止の規則・例外を確認し、必要なら直す。
2. **§4 の 3（分割の道具の試験）の後**：分割の道具と保存検査の結果を報告して止まる。
   報告に含めるもの：
   - 分割で作られたファイルの中身の要約。
   - 保存検査の出力。
   - 分割の道具が止まった（判定できなかった）箇所があれば、その一覧。

   Claude が確認してから、残り（§3.E〜G と §4 の 4〜7）に進む。

## 7. 禁止事項

- 既存の `.lean` の本文、ルートと既存の集約ファイル、監査ファイル、計画文書の変更。
- 監査や層検査の条件を弱めること。
- 他のレーンのファイルに対して、付け替えの補助を実行すること。
- 試験のための一時的な変更をコミットすること。
- main の作業木での作業・ビルド。
