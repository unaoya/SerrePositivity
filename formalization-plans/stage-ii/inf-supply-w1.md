# Codex 指示書 IS-W1：∞ 供給の第一の束（G8 の四角形、続いて G14・G9）

作成：2026-11-05 夜（段階 II の調整役）。宛先：③ ∞ 供給レーンの Codex（新しいチャット）。検収：調整役。
正本：[段階 II の計画](../stage-ii-plan-draft.md) §1・§5.1。規則：[coordination.md](../coordination.md) §2 と計画 §4 の 7 項目。

## 0. 準備

1. main（f3fcefe8e 以降）から worktree `../SerrePositivity-inf-supply`（`LEAN_Projects.nosync/` の下）と枝 `math/inf-supply` を切る。`source ~/.zshenv` の後、`lake env | grep LAKE_ARTIFACT_CACHE` でキャッシュが効いていることを確かめ、`lake build SerrePositivity.InfinityCategories.F2` で温める。
2. F-2 で名前空間が変わった宣言は、改名表 `scripts/refactor/targets/f-namespace-map.json` の新しい名前を使う（旧名は deprecated alias で残っているが、新しいファイルでは使わない）。旧 G8（`tensorSpaceFunctor_setWeightHom` 系）は deprecated。正本は `tensorSpaceFunctor_setWeightHomNatural`。
3. 読むもの：[infinity-g2-progress.md](../infinity-g2-progress.md) の末尾の二節（段 1・段 2 の途中の宣言の一覧と「残る数学的な一歩」）、[IF-G2-finish](../infinity-codex-g2-finish.md) §1（数学の位置）、[IF-G2](../infinity-codex-g2.md) §1・§3・§4（項目の型と順序）。使う側の型は BS の drafts（`formalization-plans/bhatt-scholze/drafts/Sheaves/SheafGenerators.lean`・`SpaceValued.lean`）と入口表 `bhatt-scholze/foundation-entry-points.md` §4・§4.1。
4. main の大きな束が入るたびに main を `math/inf-supply` に取り込む（調整役が知らせる。衝突は main 側を正に）。

## 1. 項目（この順）

| 段 | 内容 | 止めて報告 |
| --- | --- | --- |
| **段 1** | IF-G2-finish の②の完成：錐の辺に沿う `rightFibrationHomComparison` の全族の比較を、共通の自明 Kan fibration の span の上で作り、固定端点模型へ移す。それを `sectionsConeFamilyRestriction_fromSections`（切断制限の厳密な自然性）と合わせ、G8 別版の後段（`coherentDiagramSectionsCone` から指定極限錐への比較、`spaceUniverseValueEquivalence`、`covariantRepresentableValueEquivalence`）との一致を示す。`limitConeMap_homMk_eq_of_coneFamilyIso` に渡す全族の同型を構成する。**頂点ごとの一致だけで完成としない。必要な同型を仮定に置いた版も作らない** | **停止点 1**：主張の型（言葉で一行ずつ）、証明の要点、ビルド・F2 監査の結果 |
| **段 2** | ①：篩包含に沿う `elementsComparisonNatural` の自然性を、底を固定した相対写像空間の中で示す（`relativePreIso` で全パラメータの比較へ）。①と②を合わせて四角形（IF-G2 §3 の型：上は `sieveTensorEdge` による前合成、下は `sieveSectionsMap` による後合成、縦は `tensorSpaceFunctor_setWeightHomNatural`）を空間のホモトピー圏で閉じる | **停止点 2**：四角形の主張。調整役が取り込み、BS に知らせる（S4 の生成辺） |
| **段 3** | G14 `exists_detectingFamily`（型は IF-G2 §3。置き場所 `F2/Presentable/`、`ReflectiveModelLimitDetection` の隣） | 停止点 3（G14 だけで取り込んでよい） |
| **段 4** | G9-1〜3（Quillen A の left 版、ulift での left cofinal の保存、縮約の逆向き版。型は入口表 §4.1。置き場所 `HomotopyLimits/` か `F2/Presentable/` の既存の right 版の隣） | 停止点 4 |
| 段 5 以降 | G8 の一般の φ → G10 → G8 の一般形（IF-G2 §1・§4 の順）。**段 4 の後に調整役が範囲を確かめてから**指示書に追記する | — |

- 段 1・2 で数学的に詰まったら、通ったところまで（ビルドが通り sorry 0 の補題）を報告して止める。未完の Lean は main に入れない（枝 `math/inf-supply-wip` に置く）。
- 時間の目安：段 1・段 2 はそれぞれ半日〜2 日、段 3 は数時間、段 4 は 1 日前後。

## 2. 共通の規則

1. 新しい数学は**新規ファイルだけ**。G1・G2 の既存の宣言の本文・型・名前は変えない（どうしても要るときは止めて報告。処置は判断表の範囲で、保存比較 v3b）。
2. sorry・公理・新しい引用を残さない。
3. ビルドは小さなビルドだけ（変更したファイルと直接の importer）。始める前に `ps -axo command= | grep '[l]ake build'` が空で、`scripts/refactor/with_build_lock.sh --wait 0 -- lake build …` で鍵が取れること。全ビルド（下流・verify）はしない。
4. 新規モジュールは入口（`F2.lean` など）と監査（`scripts/audit_infinity_f2.lean` など）に登録する。監査で `importModules` を使うなら同じモジュールを `import` 行にも書く。監査は該当するものを単独で流す（`lake env lean` の前に、監査が import するモジュールを `lake build`）。
5. main の作業木では編集もビルドもしない。main への取り込みは調整役が行う（`math/inf-supply` にコミットして停止点で報告）。
6. docstring は日本語の 概要／方針／規約／使われ方（README の Conventions）。
7. 報告は段ごとに：ビルドの結果、監査、追加した宣言の名前と主張（言葉で一行ずつ）、残っている一歩（数学的に）、コミット。

## 3. 条件付きの事前承認

段 3・段 4 は、「対象のビルドと監査が通り、sorry・公理 0、既存の宣言を変えていない」なら、停止点で報告したうえで承認を待たずに次の段へ進んでよい。段 1・段 2 は主張の型を調整役が確かめるので、報告して待つ。

## 追記（2026-11-10、調整役）：G10 の範囲の注意（③ の開始前の記録）

BS-W16（⑤a、`bhatt-scholze/bhatt-scholze-codex-w16.md` §3 の 2）の Tot の欄 `ofCosimplicial_forget` は、G10（余単体的 A 加群の D(A) での Δ 上の極限は交代余面複体）を**頂点・各次数ごとではなく全関手の形で、射と指定錐まで**比べた版を要る。③ を再開するときに G10 の型をこの形にそろえる（調整役が段 4 の後の追記で範囲を確かめる）。非有界な余単体的 cdga の全比較までは G10 に含めない。

## 追記（2026-11-11、調整役）：K 理論からの使い所の注記（③ の範囲は変えない）

K の再開（`k-restart-draft.md` §3、ユーザー決定 11-11）に備えて、③ の項目のうち K 側も使うものに注記を付ける。**範囲も順序も変えない**。注記は、型を決めるときに「K の使い所でも成り立つ一般性か」を一度確かめるためのもの。

| ③ の項目 | K の使い所 | 型に求める一般性 |
| --- | --- | --- |
| G8 の四角形、G9（cofinality の left 版、ulift）、G14 | Zariski 降下の Fubini（論文 Lemma 3.2・3.3）、pro 対象の対角による添字の変更（K の経路の決定 D5） | 値の ∞ 圏を D(A) に限らない（Sp 値の前層にも当てる）。添字圏は小さい単体集合一般 |
| G10（余単体的対象の Δ 上の極限、BS-W16 の注意：全関手版・射と指定錐まで） | 点つき Kan 複体の余単体的対象の Tot（L9 の `CosimplicialTotalization`）が ∞ 極限であること。Čech 降下の実 Tot | 余単体的 A 加群だけでなく、安定 ∞ 圏（Sp）の余単体的対象にも当てられる形か、少なくとも証明の筋が Sp に移せること |
| 段 5 以降に足す：cofinality（Kerodon 7.2、Quillen A の両側） | 細分・添字の変更、pro の対角（決定 D5） | G9 の一般形として |

注記を付ける時期は段 4 の後（段 5 以降の追記と一緒）。段 1〜4 は今の指示のまま。

## 追記（2026-11-12 夜、調整役）：③-a としての再開と停止点 0 の承認

⑤c のチャットが ③-a として IS-W1 を再開した（枝 `math/inf-supply`、worktree は `../SerrePositivity-bs-classical` のまま）。段 0 の報告（`report-inf-supply-w1.md`、f1aaa0ba5：既存宣言との照合、段 1〜4 の型案・不足・配置、合計 14〜21 ファイル・約 3,050〜5,350 行）を承認する。段 1 に進んでよい。

- 置き場所は KL-W1 の後の配置（Kerodon の節、HTT）。旧 `F2/`・`HomotopyLimits/` のパスで新規ファイルを作らない。入口は現行の `Project/Entrypoints/F2.lean`、監査は `audit_infinity_f2.lean`（登録は調整役）。
- Δ・Δᵒᵖ の橋と sifted の一般部分は ③-b（IS-W2）。③-a では作り直さない。共通の錐・写像空間の部品を先に main に入れたいときは、停止点を待たず途中の取り込み点を報告してよい。
- 停止の基準は段ごとに、報告 §6 の表の各段の上端の 1.3 倍。超えそうなときは報告して止める。各停止点で見込みと実測の差を報告する。
- 段 1・2 で数学的に詰まったら、通ったところまでを報告して止める（§1 のとおり）。
