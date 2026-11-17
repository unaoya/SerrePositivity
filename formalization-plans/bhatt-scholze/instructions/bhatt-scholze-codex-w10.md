# Codex 作業指示書 BS-W10：E3 非依存化（CompletedTensor の分割）と Lemma 10.12（A8-3）

作成：2026-11-03（BS 作業チャット）。宛先：Codex。**2a の取り込み直後に開始**。基準コミット：main **`590c4eff7` 以降**（2a の取り込み。drafts の import 追従と本指示書の更新を含むコミットを開始時の基準にする）。
調整役の決定（11-03、coordination.md 588f589f3）：作業 A は 2a には入れず BS-W10 で行う。全ビルドは 2b（11-05 見込み）に便乗するので、本指示書では単体ビルドだけ。
段 1 の第一束（design-status §4 の 6、ユーザー決定 11-03）。これまでの BS-W1〜W9 と同じく worktree で行い、窓単位で進め、停止点で報告する。

## 0. 前提と方針

- **2a 後の現状（11-04 再確認）**：`completed-tensor-split.md` §0 を先に読む。CompletedTensor は同じ場所・同じ内容。有限直積の節の利用側は
  `Perfectoidization/ExcisionTor`・`Perfectoidization/FiniteComparisonExcision`・`CLMST/PerfectoidizationIsogeny/ConstantRank` の 3 本だけ。
  推奨：芯は `CompletedTensor.lean` に残し（名前不変）、有限直積を `BhattScholze/Perfectoid/FiniteProduct.lean`（新設）へ切り出す。
  2a の改名表は `scripts/refactor/targets/paper-2a-module-renames.json`・`paper-2a-declaration-renames.json`。作業 B の置き場所 `CommutativeAlgebra/UniversalHomeomorphism/`・
  `CommutativeAlgebra/EtaleStratification/` はまだ無い（新設してよい。予約済み）。

- 設計の立場（11-02 決定）：定義は原典どおり、定理は E3 に要る特別な場合だけ、差は D 番号。骨組み（`formalization-plans/bhatt-scholze/drafts/`）の docstring
  （概要／方針／規約／使われ方）を保って中身を書く。新しい `axiom` は置かない。`sorry` を残すときは理由を一行添える。
- 置き場所と名前は drafts の先頭コメントと drafts/README の表に従う。2a・2b の改名表（調整役から）で名前が変わっていたら、まず import 行を直す。
- **ビルドの規則**（coordination.md §2）：全ビルドはしない。変更したモジュールと直接の importer だけ `lake build <module>`（4a の小さなビルド：下流ビルド・verify が
  走っていない時間帯、`ps -axo command= | grep '[l]ake build'` が空であること、`with_build_lock --wait 0`）。`lake env lean` の単体確認は可。監査・verify は回さない
  （調整役が区切りで回す）。
- **触ってよい範囲**：作業 A は `SerrePositivity/BhattScholze/Perfectoidization/`（CompletedTensor とその importer の import 行、CLMST の import 行）。作業 B は新規ディレクトリ
  `SerrePositivity/CommutativeAlgebra/UniversalHomeomorphism/`・`SerrePositivity/CommutativeAlgebra/EtaleStratification/`（第一層、論文の層に予約済み、新規ファイルのみ）と
  `drafts/A8/Stratification.lean`（移した後に削除）。それ以外（他の BS ファイル、∞ 側、HA）は触らない。
- コミットは作業ごとに独立（`git add -- <paths>`、`git add -A` は不可）。メッセージ：`refactor(bs): split CompletedTensor core from the E3-dependent finite products (BS-W10 A)`、
  `feat(ca): Lemma 10.12 étale stratification (BS-W10 B, stop N)`。末尾に `Co-Authored-By` は付けなくてよい。

## 1. 作業 A：CompletedTensor の分割（2a 取り込み直後に行う。調整役の決定 11-03）

仕様は `completed-tensor-split.md` §2・§3。要点：
1. 前半 5 節を E3 非依存の芯（名前は 2a 後の Perfectoid/ の配置に合わせる）へ移し、`Derived.IntegralExistence` の import を外す。宣言名・証明は不変。
2. `isIntegralPerfectoid_finPi` を §3 の直接証明に差し替える（r = 0 は零環、r ≥ 1 は二つの直積に帰着、Fontaine 核は PreTilt・W の直積の同型で成分ごと）。
   必要な小補題（`IsAdicComplete`・`PreTilt`・`WittVector` の直積）は同じモジュールに置く。E3 を使う旧証明は削除。
3. 利用側（仕様 §0 の 3 本）の import 行を付け替える。**CLMST の 1 本（ConstantRank）は import 行だけ**（宣言・証明は触らない）。新モジュールはルート `BhattScholze.lean` に登録する。
4. 受入：仕様 §2 の到達性スクリプトが空リストを返す；変更モジュールと直接の importer の `lake build` が通る（全ビルドは 2b の 11-06 に便乗、ここでは回さない）；`scripts/audit/bhatt_scholze.lean`・`clmst.lean` を再生成して差分が import 行だけ。
- **停止点 A-1**：直接証明の小補題の型が決まり、`isIntegralPerfectoid_finPi` が `sorry` 付きで型検査を通った時点で、補題の一覧と見積もりを報告。
- **停止点 A-2**：全部通った時点で、到達性の出力・ビルドしたモジュール数・所要時間を報告して止まる。**作業 A が main に入ったら BS チャットへ知らせる**（調整役が 2b の全ビルドの前に取り込む）。

## 2. 作業 B：Lemma 10.12（A8-3、独立した古典的単位）

原典 BS 著者版 p.83 Lemma 10.12。設計 `a8-design.md` §2.3・§3.4、骨組み `drafts/A8/Stratification.lean`（決定：原典の形、noetherian 近似は表示で、Z_(p) の仮定は
`hZp : ∀ q, q.Prime → q ≠ p → IsUnit (q : R)` で、W9-III-07）。
1. `UniversalHomeomorphism/`：普遍同相（整・Spec 全射・radicial）の定義 G-A8-4、標数 p での判定（像の p 冪、核の冪零）、底変換・合成・冪零拡大での安定性、
   完全 F_p 環から被約環への普遍同相は同型（G-A8-5）。Mathlib に相当物（`RingHom.IsIntegral`、`Algebra.IsIntegral`、`PrimeSpectrum.comap` の全射・単射、
   `RingHom.FinitePresentation`）があれば使う。
2. `EtaleStratification/`：`exists_noetherianApproximation`（表示の係数で有限生成 Z_(p) 部分代数 R₀）、`generic_structure`（被約 noetherian の全商環は剰余体の有限積、
   有限被約代数は体の積、分離閉包と純非分離部分）、`spread_out_generic`（有限個の等式の分母を払い D(g₁) へ広げる、`isOpen_etaleLocus`）、
   `exists_finiteEtaleStratification`（noetherian 帰納、(pg_i, g_i) の細分）。Codex W9 第 3 部続き 2 §3.5 に紙の筋がある（被約化は底変換の後、
   p 可逆な因子は標数 0 なので純非分離部分は自明、各極小点を含む D(g₁) で V(g₁) が真に小さい）。
3. 骨組みの `True` の仮置きを本当の主張に直す。原典の (1)(2)(3) をそのまま結論にする（Thm 10.11 に要る形へ絞らない。決定 2）。
- **停止点 B-1**：定義と全主張が `sorry` 付きで型検査を通った時点（主張の形を確認する）。
- **停止点 B-2**：`UniversalHomeomorphism/` が証明済みになった時点。
- **停止点 B-3**：`exists_finiteEtaleStratification` まで通った時点。残る `sorry` があれば理由付きで一覧。

## 3. 禁止事項と受入条件

- 禁止：全ビルド、verify、監査の実行、`SerrePositivity/` の他の場所の編集、drafts の他ファイルの編集、新しい `axiom`、`git add -A`。
- 受入：各停止点で `git status --short` が作業範囲だけ；ビルドしたモジュールの一覧と時間；`sorry` の一覧（理由付き）；作業 A では到達性の空リスト。
- 原典と違う定義を入れたくなったら止めて報告（D 番号はユーザーが付ける）。

## 4. 報告してほしいこと

各停止点で：やったこと、ビルドの実測（本数・時間）、残る `sorry` と理由、原典と違えた点（あれば）、次の停止点までの見積もり。
報告は `formalization-plans/bhatt-scholze/reports/report-codex-w10.md`（新規、日本語）に追記し、報告だけのコミット `docs(bs): Codex report W10 (stop N)`。

## worktree の規則（11-05、調整役の提案）

- worktree は一度に一つ。作業 B が main に入ったら `bs-w10` の worktree は `git worktree remove` で消す（ブランチは残す）。
- 新しい worktree は `/private/tmp/` ではなく `/Users/sugakubunka/Documents/LEAN_Projects.nosync/` の下に作る（例：`../SerrePositivity-bs-w11`）。/tmp は再起動で消える。
- 停止点の間もこまめにブランチへコミットする。
