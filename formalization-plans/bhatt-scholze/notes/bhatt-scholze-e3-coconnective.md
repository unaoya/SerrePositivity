# E3 の `coconnective` 欄を外して文献入力を弱める（進捗確認チャットとの調整案）

作成：2026-10-25（BS 作業チャット）。ユーザーの了承済み（10-25）。宛先：進捗確認チャット（EInfinity 側の変更を含むため）。

## 1. 見つけたこと

主定理が BS 側で使う唯一の文献入力 `BhattScholze.Inputs.exists_perfectoidizationInterfaceE3` の型
`PerfectoidizationInterfaceE3`（`BhattScholze/PerfectoidizationInterface/Interface.lean`）は 8 つの欄を持つ。
そのうち **`coconnective`（BS Lemma 8.4：∀ S, ∀ i < 0, Hⁱ(S_perfd) = 0）はどの定理からも読まれていない**。

- E3 から環の定理を導く橋（`PerfectoidizationInterface/` の `IntegralExistence`・`InitialBridge`・`ExcisionBridge` など）が読む欄は
  perfd・unit・h0・universal・limitCone・limit_isLimit・integral・excision だけ（2026-10-25、`grep` で確認）。
- `coconnective` が現れるのは、定義（BS `Interface.lean:30`）、EInfinity の CAlg 版の定義（`EInfinity/Perfectoidization/Interface.lean:66`）、
  CAlg 版から E3 を作るときに写す一行（`EInfinity/Perfectoidization/DerivedCorollary.lean:47`）だけ。CAlg 版の欄も読まれていない。
- 当初の設計（`perfectoidization-interface.md:385`）は excision の導出で Lemma 8.4 を使う予定だったが、実装された `ExcisionBridge` は
  四頂点の離散性（`h0`・`universal` 経由）から長完全列を処理しており、`coconnective` を必要としない。

したがって今の `sorry` は、主定理に必要な主張より強い主張を仮定している。

## 2. 提案

`coconnective` 欄を E3 と CAlg 版の両方から外す。

| ファイル | 所有 | 変更 |
| --- | --- | --- |
| `SerrePositivity/BhattScholze/PerfectoidizationInterface/Interface.lean` | BS | 欄 `coconnective` の行と docstring の該当記述を削除 |
| `SerrePositivity/BhattScholze/Inputs/PerfectoidizationInterface.lean` | BS | docstring の「Lemma 8.4」の記述を「使わないので要求しない」に直す |
| `SerrePositivity/EInfinity/Perfectoidization/Interface.lean` | EInfinity（読み取り専用） | CAlg 版の欄 `coconnective` を削除 |
| `SerrePositivity/EInfinity/Perfectoidization/DerivedCorollary.lean` | EInfinity（読み取り専用） | `coconnective := F.coconnective` の一行を削除 |
| `formalization-plans/bhatt-scholze/perfectoidization-interface.md`、`infinity-categories.md`、解説の付録 A の表 | 共有の計画・解説 | 欄の一覧から外し、変更の経緯を一行記録 |

BS 側だけを先に変えると EInfinity の `toE3` が存在しない欄を埋めようとしてビルドが壊れるので、**一つのコミットで両側を変える**必要がある。
EInfinity は BS 作業チャットからは編集できないので、進捗確認チャット（または E2 レーン）で一括して行ってほしい。BS 側の 2 ファイルの差分は
BS 作業チャットで用意して渡すこともできる。

## 3. 影響

- 主定理の公理監査：変化なし（`sorryAx` の箇所は同じ一件で、主張が弱くなるだけ）。
- E3 を構成する将来の作業（BS-0 の A4）：Lemma 8.4 を界面の欄として証明する必要がなくなる。ただし原典の Cor 8.12 の証明
  （H⁻¹ の消滅）や Cor 8.14 の「連結 ⇔ 離散」で Lemma 8.4 を補題として使う可能性はあるので、A4 の作業がなくなるとは限らない。
- 確認のコマンド：変更後に `lake build SerrePositivity.BhattScholze.PerfectoidizationInterface SerrePositivity.EInfinity.Perfectoidization.DerivedCorollary`、
  BS・CLMST の領域監査、`scripts/audit_axioms.lean`（`main_statement` の公理）。

## 4. 進捗確認チャットへの連絡文（転送用）

> BS 側からの提案です（`formalization-plans/bhatt-scholze/notes/bhatt-scholze-e3-coconnective.md`）。E3 の `coconnective` 欄（Lemma 8.4）はどの橋からも読まれておらず、
> 今の `sorry` は必要より強い主張を仮定しています。EInfinity の CAlg 版の同じ欄も、E3 へ写す一行以外では読まれていません。
> E3（BS）と CAlg 版（EInfinity）の両方からこの欄を外し、`DerivedCorollary.lean:47` の一行を消す変更を、一つのコミットで行ってもらえますか。
> BS 側 2 ファイルの差分が要ればこちらで用意します。主定理の公理監査は変わりません。
