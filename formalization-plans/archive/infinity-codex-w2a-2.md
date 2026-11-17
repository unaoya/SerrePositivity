# Codex 作業指示書 IF-W2a-2：R76（Nerve まわりを HotA へ）・R77（CategoryTheory の統合）・R67（Inputs/Homotopy）

作成：2026-11-01（∞ 基盤の整備、管理は Claude）。宛先：∞ の Codex。**開始は IF-W0-4 の後**に Claude が合図する（[coordination.md](../coordination.md) §3 の #8）。
計画：[infinity-foundation-plan.md](stage-i/infinity-foundation-plan.md) の R76・R77・R67 の行、§6 の IF-W2a-2 行。伝達文 [handover §2・§3.2・§6.2](stage-i/handover-ct-to-infinity-2026-10-30.md)。
**共通の前提**：[IF-W0-1](infinity-codex-w0-1.md) §0。worktree は `../SerrePositivity-ifw0-3`、ブランチ `infra/if-w2a-2`（IF-W0-4 の取り込み後の main から）。
**一束で下流のビルドは一回**（§10.12）。CategoryTheory の基盤は HotA・EInfinity・KST・Spectra・IC の下にあるので、この束の下流はほぼ全部（約 20,000 本）。束の最後に一回だけ全ビルドし、verify を通す。

## 1. 目的

| 項目 | 内容 | 利用者（import の書き換え） |
| --- | --- | --- |
| R76 | CategoryTheory の Nerve まわり 9 本（NerveHomotopy・NerveHomotopyUniverse・NerveSimplexEndpoint・NerveSimplexStart・NerveSimplexFirstFunctor・NerveVertices・SimplexChainVertices・ElementsChainLifting・ElementsNaturalPrecomp）を `HomotopicalAlgebra/Simplicial/` へ移す。CategoryTheory ↔ HotA の相互依存が消える | HotA 26・EInfinity 12・KST 6・CT 4 |
| R77 | CategoryTheory の下位ディレクトリ 104 本（R75 の削除後は 87 本前後）と、∞ 側だけが使うトップ階層の 12 本を、伝達文 §3.2 の統合案（約 35 ファイル：Monoidal/Mod/*・TensorPower/*・Action・Braided、Enriched/*、Adjunction/Comparison、Quiver/*、Simplex/*、Under、Limits）に沿って **`merge_modules.py`（DG-W2(a) の道具。11-01 夜に main へ cherry-pick 済み：80a44df79・aee0d2b12）で統合**する。宣言・名前空間・証明は変えない | Spectra 89・HotA 50・EInfinity 25・KST 18 |
| R67 | `Inputs/Homotopy/`（KanQuillen＝引用の sorry、ResolutionHom、SimplicialLevel）を `InfinityCategories/ModelBridge/Inputs/` へ移し、`make_area_audits.py` の sorry の許可リストと scripts の check 3 本の import を直す。GroupTheory/Coxeter は IF-W0-4 で登録済みなので動かさない | check 3 本 |

## 2. 手順

1. **草案（ビルドなし）**：`targets/w2a-2.json` に R76 の move 9 件、R77 の merge（伝達文 §3.2 の表をそのまま計画に。統合先の名前は表の名前。1,700 行超が出たら報告）、R67 の move 3 件を書く。`merge_modules.py --check --max-lines 1700 --report targets/w2a-2-dryrun.md`、`validate_targets.py`（move の分）。外からの import 辺の内訳と、下流の逆閉包の本数・時間の見積もり。**止めて報告する点 1**。
2. **適用**：承認後、他の全ビルドがないことを確かめ（`with_build_lock.sh`）、main から `.lake/build` を複製（`warm_build_dir.sh`）→ before snapshot（ハッシュ版、§10.18）→ R76 → R77 → R67 の順に適用 → 内部の検証（統合先と移動先だけビルド＋保存検査）→ 外からの import の付け替え → 下流の一回ビルド → 保存検査 → **止めて報告する点 2**。
3. `layer_check.py --report`：基盤の違反（IF-W0-4 で数えた分）が R76 で消えること、CategoryTheory と HotA の相互依存が 0 であること。
4. verify（`VERIFY_JOBS` と予算は IF-W0-4 の既定）→ PASS・gate:true → **止めて報告する点 3**。
5. コミットは R76・R77・R67 で 3 本（R77 は統合先ごとではなく 1 本）。

## 3. 注意

- R77 の統合で Mathlib と重なる宣言の置き換え（伝達文 §3.3、R78）は**行わない**（窓の外、群ごとに提案 → 承認）。
- `Presentation/` は R75 で削除済み。伝達文 §3.2 の表に Presentation 由来の行があれば外す。
- 統合先の module docstring は概要／方針／規約／使われ方の様式で、元の docstring の本文は見出しの下に残す（BS 方式）。
- 束の途中では統合先・移動先だけをビルドする。全ビルドは最後の一回。

## 4. 禁止事項

- 宣言の本文・名前・名前空間の変更。R78 の置き換え。
- 論文の層の側の CategoryTheory（Abelian・Karoubi・TStructure・Triangulated など）への変更。
- 鍵なしの全ビルド。

## 5. 追記（2026-11-01 夜、草案前の不一致への回答）

1. `merge_modules.py`・`with_build_lock.sh`・`warm_build_dir.sh` と試験は DG-W2(a) の commit を main に cherry-pick した（80a44df79・aee0d2b12、新規ファイルのみ）。`infra/if-w2a-2` に main を取り込んでから使う。DG-W2(b) が後で main に merge されるとき同じ内容なので衝突しない。
2. R76 の一覧の `SimplicialChainVertices` は書き誤りで、実在名は `SimplexChainVertices`（§1 を訂正）。

このうえで §2-1 の草案を作り、停止点 1 で報告する。

## 6. 追記（2026-11-02、停止点 1 の回答：循環の解消と保留 2 件）

**承認**：草案（R76 move 9、R77 merge 26 群・95 本、R67 move 3、生成行数最大 926、move の validator PASS、下流 11,888 本・3.3〜5.0 時間）。

1. **循環 `Mod.InternalHom ↔ Mod.Closed`**：`ModuleClosed` が `ModuleInternalHomAction` と `ModuleInternalHomFunctor` の間に挟まるので、伝達文 §3.2 の表の `Monoidal/Mod/Closed`（元 `ModuleClosed` 1 本）を**廃し、`Monoidal/Mod/InternalHom` に含める**。連結順は依存どおり `ModuleInternalHom → ModuleInternalHomAction → ModuleClosed → ModuleInternalHomFunctor`。統合先は 26 → 25 群。行数は 1,700 以下のはず（超えたら報告）。
2. **`FunctorTransport`**：どの統合先にも入れず**単独のまま**（R78 で Mathlib の `Functor.copyObj` に置き換えて消す予定のファイル）。Foundation の登録（トップ階層 12 本）はそのまま。
3. **新しい統合先の Foundation 登録**：`CategoryTheory.Adjunction.Comparison` など、既存の接頭辞に入らない新しい統合先は、この束の中で `layers.json` の Foundation に加える（接頭辞 `SerrePositivity.CategoryTheory.Adjunction` を追加。他に新しい接頭辞ができればそれも）。層検査で Foundation の違反が増えないことを確かめる。
4. **`merge_modules.py --check` が循環を検出しない件**：今は道具を変えない（DG の束が同じ道具を使用中）。束の静的検査では `layer_check.py` のグラフで循環を確かめる（今回と同じ手順）。循環検出の追加は、両方の束が main に入った後の道具の回に回す。

**適用の時期**：下流 11,888 本の束は、**DG-W2(b) が main に入ってから**（coordination.md #5 の後）Claude が合図する。それまでに 1〜3 を草案に反映し、`--check`・validator・循環の再確認を済ませて止める（停止点 1′、報告は短くてよい）。

## 7. 追記（2026-11-02 13:30、内部検証の停止への回答：2 本とも「意味を変えない注釈」で直し、下流へ進む）

**受領**：R76・R77・R67 適用済み（36f9b1bd0・3ae691eba・ecc0be826）、before snapshot 273 本、内部ビルド 37 対象で失敗 2 本、外部利用者 92 ファイルの保留、鍵の解放。宣言の変更に当たるか不明な失敗で止めた判断は正しい。

**原因**（Claude が 11-02 13:00 に `ifw0-3` の after 環境で探針を `lake env lean` して再現。本番ファイルは触っていない）：

1. `Reedy/RelativeBoundaryFunctor` 158・169 行：R77 の統合先の import の和で Mathlib の `_root_.Functor.map_id`（`Mathlib/Control/Basic.lean`、applicative の補題）が閉包に新たに入り、`open CategoryTheory` の下の `Functor.map_id` の解決が変わった。DG-W2 §14 と同型。
2. `Spectra/ModelCategory/SimplicialLevel` 45 行：`exact levelModelCategoryOfMonoidalGenerators PointedSimplicialSet.circle …` の `circle` の宇宙がメタ変数 `?u` のまま instance 合成に入り、`MonoidalCategory PointedSimplicialSet.{?u}` → `PointedObject.smashMonoidalCategory` → `HasFiniteColimits (Type ?u)` → `hasFiniteColimits_of_hasColimits` → `Types.hasColimitsOfSize [UnivLE.{?u, ?u}]` → `univLE_of_max` → `UnivLE.zero : UnivLE.{0, v}` が **`?u := 0` を代入**する。以後 `C = PointedSimplicialSet.{0}`・`w = 0` となって `Cardinal.aleph0.{u}` が合わず、局所 instance `ModelCategory PointedSimplicialSet.{u}` も見つからない。before 環境では同じ合成がこの経路に入らなかった（import の和で環境に入る instance の集合と順序が変わる。同じ優先度の instance は環境で後に来るものから試される）。名前の問題ではないので完全修飾で直らないのは当然。

**処置**（承認。宣言の型・本文・名前は変えない注釈で、保存比較のハッシュ一致で同一を証明する）：

1. `RelativeBoundaryFunctor`：2 箇所を `CategoryTheory.Functor.map_id` に完全修飾。
2. `SimplicialLevel`：`exact` の引数を `PointedSimplicialSet.circle.{u}` にする（同じファイルの直前の `let` 行と同じ書き方）。67 行の `levelModelCategoryOfMonoidalGenerators_generated PointedSimplicialSet.circle …` も `circle.{u}`。Claude の探針では `circle.{u}` だけで通り、定数の宇宙を明示する `levelModelCategoryOfMonoidalGenerators.{u, u + 1, u}` でも通った。前者を採り、保存比較で `simplicialLevelModelCategory` の本体ハッシュが一致しなければ後者を試す。
3. コミットは別に 1 本「修飾・宇宙の明示」（R67 の後、`git commit --only`）。

**判断表への追加**（IF-W0-3 §10.31 の拡張。この束と以後の束、DG-W3 でも有効）：「補充の import」「完全修飾」に加えて、**「宇宙の明示」**（引数や定数への `.{u}` の付加）と**「名前付き引数の明示」**を、宣言の意味を変えない処置として許す。条件は同じ：before/after の保存比較で一致（def は本体も、theorem は型。道具の既定）、別コミット、報告に一覧。一致しなければ止める。背景：import の和で環境の instance の集合と順序が変わると、宇宙メタ変数が別の instance に捕まることがある。名前の隠蔽と同じ「環境が広がったことによる elaboration の変化」であり、宣言の意味は変わらない。

**再開の手順**：

1. 処置 1・2 を当て、内部ビルド（37 対象）を再実行。失敗が残れば判断表（補充・修飾・宇宙の明示）で。新しい型の失敗は止めて報告。
2. 内部の保存比較（273 本）。処置した宣言（`domainMap_id`・`codomainMap_id`・`simplicialLevelModelCategory`・`simplicialLevelModelCategory_generated`）は報告で個別に挙げる。
3. 保留した 92 ファイルを `deferred-imports.json` の hash で確かめて HEAD の内容へ戻す（報告の手順どおり。一括 reset はしない）。
4. 下流の一回ビルド（11,818 本、鍵のもと）→ 保存比較 → **停止点 2**。条件 5 は失敗モジュール数で（IF-W0-3 §10.33）。論文の層の worktree（`SerrePositivity-refactor-1-4`）の小さなビルドは、下流ビルドの間 Claude が止めてもらう。
5. 層検査（§2-3）→ verify → **停止点 3**（見込み 11-02 夜）。

## 8. 追記（2026-11-02 14:00、保存比較の停止への回答：証明無関係を項の水準へ（v3）、FunctorialExtension の修飾を承認、下流ビルドは先に始める）

**受領**：§7 の 4 宣言のうち `simplicialLevelModelCategory` の本体不一致（`circle.{u}` 案・`.{u, u + 1, u}` 案とも同じハッシュ）、2 モジュールで 9 宣言の不一致、`FunctorialExtension:68` の同型の失敗、92 ファイル保留、コミットなし。§7 の条件どおりの停止で正しい。

**診断**（Claude、`w2a-2-section7-comparison.json` と `decl_snapshot.lean` の読み取りから）：9 件はすべて **Prop 型の部分項（instance の証明）の導出経路の違い**として説明がつく見込み。

- 修正していない `simplicialLevelI`・`simplicialLevelJ`（abbrev）の本体や、`codomainMap_fst` など 4 補題の型、`…_fibrations`・`…_weakEquivalences` の型まで不一致なのは、ソースではなく環境の違いによる。`levelGenerators`・`pullback.fst` などの `[HasColimitsOfSize …]`・`[HasPullback …]` の引数（Prop の class の instance）が、before と after で別の instance の連鎖で合成された（§7 の原因 2 と同じ機構：import の和で環境の instance の集合と順序が変わる）。`_proof_7` → `simplicialLevelI._proof_1` も、abbrev から切り出された補助証明の名前の違いで同じ種類。
- 現行の道具（v2）は**定数**の水準でしか証明無関係にしていない。theorem 定数は型で置き換えるが、`@thm₁ args₁` と `@thm₂ args₂` という同じ命題の異なる証明は `app` の構造が違うので不一致になる。核では Prop は証明無関係（definitional）なので、宣言の意味は変わっていない。
- データの instance（`MonoidalCategory` など）は同じ定数 `PointedObject.smashMonoidalCategory` で、違いは Prop の引数だけのはず。これを機械で確かめるのが下の v3。

**処置**：

1. **`FunctorialExtension:68` の 2 箇所**：`CategoryTheory.Functor.map_id` へ完全修飾（承認。コミット「修飾・宇宙の明示」に含める）。内部ビルドで同型の失敗が他に出ても同じ扱い。
2. **道具 v3：項の水準の証明無関係**。`snapshot` は既に `CoreM` なので `MetaM` に持ち上げ（`(… : MetaM _).run'`）、`fingerprint` の前に証明を消す：
   ```lean
   def eraseProofs (e : Expr) : MetaM Expr :=
     Meta.transform e (pre := fun e => do
       let isPrf ← try Meta.isProof e catch _ => pure false
       if isPrf then return .done (← instantiateMVars (← inferType e)) else return .continue)
   ```
   `Meta.transform` は束縛子の下を fvar で開いて `mkLambdaFVars` で閉じ直すので、閉じた項に `isProof`（型が命題か）を使える。証明の部分項はその**型**（命題）の digest に置き換わる。theorem 定数の型置換（v2）は残してよい（v3 に包含される）。`generatedDefinition` の値展開もそのまま。`hash_algorithm` を `… proof-irrelevant v3 (term-level)` にする。性能：`inferType` は MetaM 内でキャッシュされる。巨大な項（R80 の候補）で時間が倍以上になったら報告するが、まず試す。
   試験：`test_proof_irrelevant_compare.py` に (a) 同じ命題の 2 つの証明（instance 連鎖の違い）で def の本体 digest が一致、(b) データの引数が違えば不一致、(c) 束縛子の下の証明も消える、を加える。
   `decl_snapshot.lean` は ∞ の道具なので ∞ が直してよい（§6-4 の「今は道具を変えない」は `merge_modules.py` の循環検出の話）。DG-W3 が始まる前に main へ cherry-pick する。
3. **順序（時間を使わないため）**：処置 1 を当てて内部ビルドを通す → **92 ファイルを hash 確認のうえ HEAD へ戻し、下流ビルド（11,818 本、鍵）を先に始める** → その間に v3 を作る（ビルド不要）→ before 環境を cache から scratch に復元して v3 の before/after snapshot（273 本）を取り直し、比較（snapshot はビルドではないので鍵の外でよいが、下流ビルドと CPU を分け合うので 16 本並列は 8 本に落とす）→ 残りは §10.34〜10.35 で個別に照合 → 停止点 2 の報告に、v2 で不一致だった 9 件が v3 で一致したこと（しなければその理由）を明記する。
   根拠：9 件はすべて Prop の経路の違いと説明でき、下流ビルドは比較の結果に依存しない。万一データの違いが見つかって修正が要っても、Lake キャッシュで影響範囲の再ビルドだけで済む。
4. **停止条件の言い換え**（§7 の「一致しなければ止める」の精密化。以後の束と DG-W3 でも有効）：同一とは **v3（証明を消した項）の digest の一致**。v3 でも不一致で、差がデータ（Type 水準の部分項、instance のデータ、宇宙）にあるなら止める。v2 だけの不一致は止めない。

**報告してほしいこと（停止点 2）**：v3 の実装の要点と試験、273 本の before/after 比較の結果（v2 の 9 件の行方）、下流ビルドの round の表、補充・修飾・宇宙の明示の件数と一覧。

## 9. 追記（2026-11-02 14:00、v3 の残り：証明は型ではなく標識に置き換える（v3b）、`_proof_N` は def の親にも束ねる）

**観察**（Claude、`section8/annotations-{before,after}-v3.json` の読み取りと、before scratch・after の `#print` の比較）：v3（証明の部分項をその型に置換）で Reedy の 4 補題の型は一致したが、`SimplicialLevel` の `simplicialLevelI`・`simplicialLevelJ`・`simplicialLevelModelCategory` の本体、`…_fibrations`・`…_weakEquivalences` の型、`_proof_1〜6` の型が残った。`pp.explicit true`・`pp.universes true`・`pp.proofs false` で `simplicialLevelI` を before/after で印字すると**バイト単位で一致**（28,288 バイト）するので、差は証明の部分項の中だけにある。

**原因**：`simplicialLevelI._proof_1` の型（命題）が before では `HasFiniteColimits SSet.{u}`、after では `HasFiniteColimits (SimplexCategoryᵒᵖ ⥤ Type u)`（`SSet` を展開した形）。after の instance 連鎖 `instHasFiniteColimitsFunctor` は結果の型を関手圏の形で述べるため、**定義的には等しいが構文的には違う命題**になる。v3 は証明を `inferType` の結果に置き換えるので、この構文の差がハッシュに残る。核の受け入れた項である以上、命題は文脈（関数の束縛子の型と他の引数）で決まっている。

**処置 v3b**：証明の部分項は型ではなく**固定の標識**に置き換える（`pp.proofs false` が `⋯` にするのと同じ）：

```lean
def DeclSnapshot.eraseProofs (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    let isPrf ← try Meta.isProof e catch _ => pure false
    if isPrf then return .done (mkConst `_erased_proof) else return .continue)
```

健全性：引数の位置の証明の命題は関数の型と他の引数（どちらもハッシュされる）で決まり、`let`・λ の束縛子の型もハッシュされるので、標識に置き換えても「データが同じで命題だけ違う」二つの項が同一視されることはない。theorem 自身の型は従来どおり別にハッシュする。`hash_algorithm` を `… v3b (term-level, proof marker)`。試験：§8 の (a)(b)(c) に加え (d) 命題が定義的に等しく構文的に違う証明（`SSet` と展開形）で本体 digest が一致。

**`compare_snapshots.py`**：`_proof_N` の束ね（110〜122 行）は親が theorem のときだけなので、**親が def・abbrev・instance でも束ねる**：親の型・本体が一致していれば `_proof_N` の型の差は報告しない（v3b では親の本体から証明が消えているので、補助定理の命題は親の同一性に関係ない）。親が不一致なら従来どおり両方報告。

**手順**：v3b を別コミット（道具・試験）→ 取りかけの v3 の before shard（18/37）は捨て、before scratch から v3b で 273 本を取り直す → after も v3b → 比較。下流ビルドはそのまま続ける（並列は 8 本）。停止点 2 の報告に、v2 の 9 件と v3 の残り 12 件の行方を書く。v3b でも残るものがあれば、それはデータの差なので止める。

## 10. 追記（2026-11-02 15:30、停止点 2 の承認：層検査と verify へ）

**承認**：下流 round 1（11,550 本、1 時間 55 分）PASS、v3b の保存比較（273 → 203 本、2,033 宣言）不一致 0、修飾した 3 モジュールの 35 宣言一致、v2 の 9 件・v3 の 12 件の行方の説明、補充 0・完全修飾 4・宇宙の明示 2、ログ 34 本にエラー・PANIC 0。コミット 515c71147・a4274406b・56ee73f32・7c127089b。

**次**：
1. §2-3 の層検査を after の最終状態で再実行して記録：Foundation の違反 0、CategoryTheory ↔ HotA の相互依存 0（R76 の目的）、W1/W2a/W2b の禁止モジュール数が 1/166/166 から増えていないこと、ratchet の基準を取り直す。
2. verify：`VERIFY_JOBS=6 VERIFY_MEMORY_GB=40 zsh scripts/refactor/verify.sh`（gate:true、鍵のもと。他の全ビルドがないことは Claude が確認済み：15:30 時点で `lake build` なし）。IF-W0-4 の実測（RSS 最大 50.8 GB > 45）に合わせて予算は 40。
3. **停止点 3**：verify の summary（PASS・gate:true、実時間、最大同時 RSS、待ちの発生）、層検査の前後、コミット一覧、`audit-stats.json` の更新の有無。取り込みは Claude が行う（main へ merge → キャッシュから温め → 論文の層へ「全ビルド可」）。
