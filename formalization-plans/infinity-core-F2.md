# F2：F2-lite と presentable ∞ 圏（v2、F1b・N 分担）

作成日：2026-10-18。更新日：2026-10-19。
正本は [foundations.md](foundations.md)。本書は F2-lite と F2 後半の正本。
F1b の前提工程は [infinity-core-F1b.md](infinity-core-F1b.md)、
N の γ3・γ4 は [e-infinity-algebras.md](e-infinity-algebras.md) を参照する。

## 引き継ぎ（2026-10-19）

### 現在地

- v2 の F2-lite 第 1 部を F1b が担当する。実装の順序は B4 → B5 → F2-lite 第 1 部。
- F2 固有の Lean モジュールは未着手。
- Cat_∞ の構成は F1 に既存：`F1/QCatSimplicial.lean` と `F1/CatInfinity.lean`。
  関手 ∞ 圏の core を Hom とする QCat は局所 Kan、γ1 を用いた coherent nerve は quasicategory。
  再定義せず、F2 の入力として再利用する。対象ビルド成功（1671 jobs）。
- Cat_∞ の引き戻しの普遍性・lax pullback の構成と普遍性は未完了。
  これらは Cat_∞ の quasicategory 性だけから完了とは扱わない。

### 残り（依存順、実作業時間の概算）

- F1b：B4・B5（残りと見積もりは F1b 計画が正本）。
- F2L-1：既存 Cat_∞ の対象・辺と QCat、写像空間と Fun の core の比較 API を確認・整備。
  Kerodon Construction 5.5.3.1、Proposition 5.5.3.3・§5.5.3。8〜24 時間。
- F2L-2：Cat_∞ の引き戻しを実際に構成し、写像空間の普遍性を証明。
  Kerodon §5.5.3、HTT §3.3.3、Tamme §1 Remark 7。40〜100 時間。
- F2L-3：Fun(Δ¹,C) と端点評価から lax pullback を構成し、quasicategory 性と普遍性を証明。
  Tamme §1 Definition 5・Remark 6。24〜60 時間。
- F2L-4：引き戻しを lax pullback の同値辺上の全部分 ∞ 圏と同定し、
  安定性・exact 関手への接続界面を整備。Tamme §1 Remark 7・Lemma 8(i)(iv)。24〜60 時間。
- N：filtered 余極限、Ind、compact、冪等完備化、Ind の安定性・compact 生成。
  HTT §5.1.4・§5.3、Kerodon 9。細分化・見積もりは N の着手時に確定する。
- I-b：presentable・随伴関手定理を F1b、Bousfield 局所化・P_Σ を N と分担。
  HTT §5.5、Kerodon 9。F2-lite の後に細分化する。

### 主要宣言（実装済みの名前のみ）

- `QCat`
- `qCat_sHom`
- `qCat_sHom_kanComplex`
- `CatInfinity`
- `catInfinity_quasicategory`
- `CatInfinityFunctor`
- `catInfinityFunctor_quasicategory`
- `SpaceInfinity`
- `spaceInfinity_quasicategory`

### 依存と提供

- F1 の QCat・CatInfinity、Core の関手 ∞ 圏・core・写像空間・極限、γ1 を読み取り専用で使う。
- γ3・γ4 は N が提供。𝒮 の極限・余極限の比較を重複実装しない。
- 提供先：D の β4（dg gluing と lax pullback の比較）、K-基盤の Cat^perf・Tamme。
- N と共有：宇宙、Cat_∞ の極限の界面、Ind・冪等完備化と接続する普遍性。

### 未コミット

- 本書は F1b の今回の保存単位に含める。保存コミット後の F2 所有ファイルの変更はなし。

### 既知の問題

- 既存の単体集合としての strict pullback と、Cat_∞ 内の引き戻しを区別する必要がある。
- Tamme のモデル構造を用いた説明は原典の参照にとどめ、主経路は内ホーン充填・
  categorical fibration の直接的 API と写像空間の普遍性で証明する。

### 次の一手

- B4・B5 の完了後、`F1/CatInfinity.lean`・`F1/QCatSimplicial.lean` と
  coherent nerve の頂点・辺・写像空間比較を読み、F2L-1 の不足分を決める。

## 0. 目標と範囲

| 工程 | 担当 | 到達点 | 原典 |
| --- | --- | --- | --- |
| F2L-1 | F1b | Cat_∞ の既存 coherent nerve 模型と比較 API | Kerodon §5.5.3 |
| F2L-2 | F1b | Cat_∞ の引き戻しと写像空間による普遍性 | Kerodon §5.5.3、HTT §3.3.3 |
| F2L-3 | F1b | 矢印 ∞ 圏を使う lax pullback | Tamme §1 Definition 5・Remark 6 |
| F2L-4 | F1b（D と接続） | 通常の引き戻しとの比較、安定性・exact 関手の界面 | Tamme §1 Remark 7・Lemma 8 |
| F2L-N | N | filtered、Ind、compact、冪等完備化、Ind の安定性 | HTT §5.1.4・§5.3、Kerodon 9 |
| F2 後半 | F1b・N | presentable、随伴関手定理、Bousfield 局所化、P_Σ | HTT §5.5、Kerodon 9 |

F2-lite の範囲に presentable・Pr^L のテンソル積・HA §4.8 は含めない。
Tamme の分裂定理・Verdier 列・Land–Tamme の主定理は K-基盤、dg gluing との比較は D の β4。

## 1. 設計と受入条件

- 新規配置は `SerrePositivity/InfinityCategories/F2/`。F1 の既存公開名を保持する。
- 宇宙：小 ∞ 圏の単体は `SSet.{u}`、`CatInfinity.{u}` は `SSet.{u+1}`。
  Cat_∞ 内の図式と、元の小 ∞ 圏間の関手の宇宙を明示する。
- `CatInfinity = SimplicialNerve QCat`、QCat の Hom は `core Fun(C,D)`。
  Hom に全ての自然変換を含む模型は別の構造なので代用しない。
- Cat_∞ の引き戻しの構成では、対象と射の表示に加えて、全ての試験 ∞ 圏からの
  写像空間が空間の引き戻しを与えることを証明する。hCat だけの普遍性で完了としない。
- `p : A → C`、`q : B → C` に対し、lax pullback は
  `(A × B) ×_(C × C) Fun(Δ¹,C)`。端点評価は `(source,target)`、矢印は `p(a) → q(b)`。
  元の引き戻しは、矢印が同値である対象の張る全部分 ∞ 圏として比較する。
- 単体集合の strict pullback が使える箇所では、端点評価の充填性と、その strict pullback が
  Cat_∞ の引き戻しを表すことを証明してから使う。
- 安定性は有限極限・有限余極限と exact 関手の保存を通じて接続し、
  dg gluing との比較・分裂定理を定義のフィールドとして仮定しない。
- 追加公理・sorry・文献入力は導入しない。許す公理は標準三公理のみ。
  新しい主経路に `ModelCategory SSet` 等の instance 仮定を置かない。
- 保存単位ごとに対象ビルド、公理監査、主経路の instance 仮定の検索を実施。
  検証済みの構成・普遍性・比較の範囲を別々に現在地へ反映する。

## 2. 原典

- [Kerodon §5.5.3](https://kerodon.net/tag/0208)：QCat の coherent nerve と ∞ 圏の ∞ 圏。
- [Kerodon Proposition 5.5.3.3](https://kerodon.net/tag/020B)：局所 Kan 性からの quasicategory 性。
- [Tamme 2018 §1](https://arxiv.org/html/1703.03331v3#S1)：Definition 5、Remarks 6–7、Lemma 8。
- HTT §3.3.3（∞ 圏の極限）、§5.3（Ind・compact）、§5.5（presentable）。

実施記録はコミットメッセージ。本書には現在地と設計を置き、長い型一覧を追記しない。
