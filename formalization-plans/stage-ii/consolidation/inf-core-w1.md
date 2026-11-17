# Codex 指示書 IC-W1：∞ 中核の第一の束（Verdier：M1・M2・M7）

作成：2026-11-05 夜（段階 II の調整役）。宛先：① ∞ 中核レーンの Codex（新しいチャット）。検収：調整役。
正本：[段階 II の計画](../../stage-ii-plan-draft.md) §2（B-1）・§5.1。項目の定義は [infinity-foundation-plan.md](../../archive/stage-i/infinity-foundation-plan.md) 段 G の M1・M2・M7〜M9 と [refactoring-verdier.md](../../archive/stage-i/refactoring-verdier.md) §5。規則は [coordination.md](../../coordination.md) §2 と計画 §4。

## 0. 目的

K 基盤 1（B-3）の入口になる、安定 ∞ 圏の Verdier 商の一般論を Stable/Verdier に作る。いまある Verdier 商は dg 版だけ（`Derived/` の `dgQuotientNerve_isStable` など）。一般の安定 ∞ 圏について次の三つを示す：束ねた Verdier 列が安定版の Verdier 列であること（M1）、cofiber 辺による局所化が安定であること（M2）、商が存在すること（M7）。

## 1. 準備

1. main（f3fcefe8e 以降）から worktree `../SerrePositivity-inf-core`（`LEAN_Projects.nosync/` の下）と枝 `math/inf-core` を切る。`source ~/.zshenv` の後、`lake env | grep LAKE_ARTIFACT_CACHE` でキャッシュが効いていることを確かめ、`lake build SerrePositivity.InfinityCategories.Stable` で温める。
2. F-2 で名前空間が変わった宣言は、改名表 `scripts/refactor/targets/f-namespace-map.json` の新しい名前を使う（旧名の deprecated alias は新しいファイルでは使わない）。
3. 既存の材料：`Stable/Verdier/VerdierSequence.lean`（束ねた `IsVerdierSequence`。名前空間は `KST.LocalizingInvariants` のまま）、`Stable/Verdier/StableVerdierSequence.lean`（`IsStableVerdierSequence`）、`Stable/Verdier/Fractions/`（分数の比較）、`Stable/Exact/ExactFunctorDescent.lean`（`isExactFunctor_of_precomp_arrowLifts`）、`KST/LocalizingInvariants/GeneralLocalization.lean`（`exists_quasicategory_localization`、宇宙は同じ `SSet.{u}`）、`Derived/Gluing/*ThickClosure*`（`thickClosure`）。dg 版の議論（`Derived/DGQuotient*`・`Derived/ResolvedDGQuotientStability.lean`）は一般化の手本。
4. main の大きな束が入るたびに main を取り込む（調整役が知らせる。衝突は main 側を正に）。

## 2. 段と止めて報告する点

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| **段 0（紙）** | M1・M2・M7 の紙の筋を書く：主張の Lean の型（既存の構造体のどちらで述べるか、宇宙）、既存の宣言で使えるもの、新しく要る補題、規模の見込み。M2 では、いまの分数の比較（`VerdierSpanCoherentContraction` など）が「商が安定」「`IsVerdierSequence`」を仮定しているので、それらを使わない部分を切り出せるかを判定する。M7 は (a)（一般の部分圏、核は厚い閉包）と (b)（像が厚いとき `IsVerdierSequence`）に分け、(a) に M9（一般の `thickClosure` と dg 版の比較）が本当に要るかを確かめる | **停止点 0**：紙の筋。調整役が範囲を確かめる |
| **段 1** | M1：`IsVerdierSequence` ⇒ `IsStableVerdierSequence`（DK 局所化の普遍性を完全関手に制限する。完全性の判定は `isExactFunctor_of_precomp_arrowLifts`、矢の持ち上げは分数表示から） | **停止点 1**：主張・ビルド・監査 |
| **段 2** | M2：安定 ∞ 圏 B の安定な充満部分圏の cofiber 辺による局所化は安定で、局所化関手は完全（一般形。任意の局所化については言えないので仮定を明記） | **停止点 2** |
| **段 3** | M7 (b)、続いて (a)（段 0 の判定で M9 が要るなら M9 を先に） | **停止点 3**：ここで束を区切り、調整役が取り込む。K 理論レーン（B-3）の開始の判断に使う |
| 後続 | M8（商の関手性。最初の検討事項は infinity-foundation の解説第 5 章 §5）、L4（R57：分数の Weak*・Tamme* の 4 対を一つの一般版に。入力 `scripts/refactor/targets/w2c-stage-g-input.json`） | 段 3 の後に調整役が指示書に追記する |

- 時間の目安：段 0 は数時間、段 1 は半日〜1 日、段 2・段 3 はそれぞれ 1〜3 日。
- 数学的に詰まったら、通ったところまで（ビルドが通り sorry 0 の補題）を報告して止める。未完の Lean は main に入れない（枝 `math/inf-core-wip` に置く）。

## 3. 共通の規則

1. 新しい数学は**新規ファイルだけ**、置き場所は `Stable/Verdier/`（必要なら `StablePresentable/`）。既存の宣言の本文・型・名前は変えない（要るときは止めて報告。処置は判断表の範囲で、保存比較 v3b）。
2. 層の順序を守る（`InfinityCategories/README.md` と layers.json）。Stable から KST・ModelBridge・HA のモデル圏を import しない。いま Stable/Verdier から KST の名前空間の宣言を使うのは構わないが、新しく KST のディレクトリのモジュールを import しない。
3. sorry・公理・新しい引用を残さない。
4. ビルドは小さなビルドだけ（変更したファイルと直接の importer）。始める前に `ps -axo command= | grep '[l]ake build'` が空で、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build …` で鍵が取れること。全ビルド（下流・verify）はしない。
5. 新規モジュールは入口（`Stable/Verdier.lean`）と該当する監査に登録する（`importModules` を使う監査は `import` 行にも書く）。監査は単独で流す。
6. main の作業木では編集もビルドもしない。main への取り込みは調整役が行う。
7. docstring は日本語の 概要／方針／規約／使われ方。
8. 報告は段ごとに：ビルドの結果、監査、追加した宣言の名前と主張（言葉で一行ずつ）、残っている一歩、コミット。

## 4. 条件付きの事前承認

段 1 は、停止点 0 で調整役が型を承認した後なら、「対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない」ときに報告したうえで段 2 へ進んでよい。段 2 から段 3 も同じ。段 3 の区切りでは止まる。
