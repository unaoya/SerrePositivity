# α2b：随伴・局所化・Kan 拡張

作成日：2026-10-18。正本は [infinity-core-F1.md](infinity-core-F1.md) の F1e〜F1g と
[foundations.md](foundations.md) §4。本計画はその担当部分の型・工程・現在地を管理する。

## 0. 目標と範囲

quasicategory の随伴、反射的局所化、cofinality、点ごとの左右 Kan 拡張を構成する。
`SerrePositivity/InfinityCategories/F1B/` に置き、namespace は
`SerrePositivity.InfinityCategories`。集約は `InfinityCategories/F1B.lean`。
Core/・F1/・Stable/ は読むだけとし、straightening に依存しない。
sorry・追加公理・文献入力は使わない。実施の経緯はコミットメッセージに記録する。

## 1. 原典と工程

| 工程 | 成果 | 原典 |
| --- | --- | --- |
| B1 | 単位・余単位と h Fun の三角恒等式、写像空間との特徴づけ、合成、随伴関手の一意性 | Kerodon [Def 6.1.1.1](https://kerodon.net/tag/02CG)、[§6.1.3](https://kerodon.net/tag/02D5)、[§6.1.5](https://kerodon.net/tag/02DM)、[Def 6.2.1.1・Prop 6.2.1.17](https://kerodon.net/tag/02EJ)、[Cor 6.2.6.5](https://kerodon.net/tag/02FX) / HTT §5.2 |
| B2 | 充満部分単体集合への反射、局所対象、冪等性、反射的局所化の普遍性 | Kerodon §6.2.2–6.2.4、[§6.3.1](https://kerodon.net/tag/01ME)・§6.3.3 / HTT §5.2.7 |
| B3 | right cofinal の定義、Quillen A、A2h の始対象による極限計算との整合 | Kerodon Def 7.2.1.1、[Thm 7.2.3.1](https://kerodon.net/tag/02NX) / HTT Thm 4.1.3.1 |
| B4 | slice の極限による左右 Kan 拡張、h での一意性、各点の存在 | Kerodon [Notation 7.3.1.1・Def 7.3.1.2](https://kerodon.net/tag/02Y7)、§7.3.5 / HTT §4.3 |
| B5 | nerve による古典随伴・Kan 拡張の回収、公理監査 | 上記と通常の圏の随伴・Kan 拡張 |

## 2. 設計上の決定

- 随伴の二胞体は h((ihom X).obj Y) の射。`SSet.QCat.strictBicategory` と
  `CategoryTheory.Bicategory.Adjunction` を使い、hX と hY の間の随伴だけで代用しない。
  A1c の `homotopyNatTrans`、A3a の `FunctorIso` との接続を公開する。
- 写像空間の特徴づけでは `pinchedHom` の自然なホモトピー同値を扱う。
  π₀ の全単射だけ、または各点で任意に選んだ同値の族だけでは B1 完了としない。
- 局所化の普遍性は、W を可逆辺へ送る関手の充満部分 ∞ 圏への前合成同値。
  一般の C[W⁻¹] の存在は F2 に委ね、ここでは反射的な場合を構成する。
- right cofinal は colimit を計算する向き。始対象による limit 計算は双対の
  left cofinal と対応する。この向きを B3 で明示し、A2h を逆向きに引用しない。
  Quillen A の fiber 条件は **弱可縮性**であり、Kan 性・圏としての可縮性に強めない。
- B4 は各点の slice 極限を使う。点ごとの存在と関手全体への組み立てを区別し、
  後者（Kerodon §7.3.5）は A6 の関手 ∞ 圏の極限 API が揃ってから証明する。
- 監査 `scripts/audit_infinity_f1b.lean` は宣言元モジュールで抽出し、依存公理は
  propext・Classical.choice・Quot.sound の三つだけを許す。

## 3. 現在地

B1 の基礎部分を実装中。単位・余単位、三角恒等式、恒等随伴、合成、左右随伴の
h Fun での一意性、およびパラメータ付きの二胞体の adjunct 対応を実装した。
これは B1 全体の完了ではない。写像空間の特徴づけは順向き Prop 6.2.1.17、
逆向き Cor 6.2.6.5 に分け、自然性を含めて証明する。A1c の自然変換と
`qcatCellOfHomotopy` の評価が一致する比較も未完了。B2〜B5 は未完了。
対象ビルド（1577 jobs）・公理監査（27 宣言、標準三公理のみ）は成功。

## 4. 主要宣言

すべて namespace `SerrePositivity.InfinityCategories`。

| 宣言 | 型・役割 | 状態 |
| --- | --- | --- |
| `qcatOf`・`qcatMap` | 単体集合と射を `SSet.QCat` の対象・一胞体として表示 | 実装済み |
| `QCatAdjunction F G` | `Bicategory.Adjunction (qcatMap F) (qcatMap G)` | 実装済み |
| `qcatHomFunctor X Y` | 双圏の Hom 圏 → h((ihom X).obj Y) | 実装済み |
| `qcatCellEquiv F G` | 双圏の二胞体 ≃ h Fun の Hom | 実装済み |
| `functorEdgeOfHomotopy`・`qcatCellOfHomotopy` | X⊗Δ[1]→Y を辺・二胞体として表す | 実装済み |
| `qcatIsoToFunctorIso` | 双圏の同型 → Core の `FunctorIso` | 実装済み |
| `QCatAdjunction.refl` | 恒等関手の自己随伴 | 実装済み |
| `QCatAdjunction.comp` | F⊣G と F′⊣G′ から (F≫F′)⊣(G′≫G) | 実装済み |
| `QCatAdjunction.unitHom`・`counitHom` | 単位と余単位を h Fun の射として表示 | 実装済み |
| `QCatAdjunction.left_triangle_hom`・`right_triangle_hom` | 単位子を含む h Fun での三角恒等式 | 実装済み |
| `QCatAdjunction.rightAdjointIso`・`leftAdjointIso` | 共通の随伴を持つ一胞体間の同型 | 実装済み |
| `QCatAdjunction.rightAdjointFunctorIso`・`leftAdjointFunctorIso` | 同じ一意性を既存の FunctorIso 型で公開 | 実装済み |
| `QCatAdjunction.homEquiv a U V` | h Fun(Z,Y)(U≫F,V) ≃ h Fun(Z,X)(U,V≫G) | 実装済み |
| 写像空間による特徴づけ | 自然な pinchedHom のホモトピー同値との同値 | 未完了 |
| B2〜B5 | §1 の全項目 | 未着手（監査スクリプトは作成済み） |
