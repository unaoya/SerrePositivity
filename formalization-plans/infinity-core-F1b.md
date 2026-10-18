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
  中間模型には既存の `F1.IntervalMappingSpace` を使う。この小さいモジュールへの
  推移的 import は straightening を含まない。端点の補助計算は F1B 内に置き、
  `F1.IntervalFatDiagram` の広い集約への依存は作らない。
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

B1 を実装中。単位・余単位、三角恒等式、恒等随伴、合成、左右随伴の
h Fun での一意性、パラメータ付き adjunct 対応とその二変数の自然性を実装した。
A1c の `homotopyNatTrans` と `qcatCellOfHomotopy` の評価の一致も証明した。
区間模型への族 A→Map(x,y) と Fun(A,X) の定値関手間の辺は厳密に全単射で、
この族から h Fun の定値関手間の Hom への写像は全射である。
`intervalFamilyHom f = intervalFamilyHom g` なら族 f,g の間に実際の単体的ホモトピーが
存在することを証明した。構成は、h Fun の射の等式を右ホモトピーの三角形へ戻し、
四辺を計算した正方形へ引き戻して区間族を転置するもの。
QCat の whisker と内部 Hom の前合成の一致も証明し、adjunct のパラメータ自然性に接続した。
定値関手の後合成の同一視を補った `constantHomEquiv` はパラメータ自然な全単射である。
この全単射から区間模型の比較射・逆候補を作り、両合成が恒等射に実際にホモトピックである
ことを証明した（`intervalMap_isSimplicialHomotopyEquivalence`）。比較射が任意の
quasicategory パラメータ族の adjunct を表す公式と、その仕様によるホモトピー一意性も公開した。

これは B1 全体の完了ではない。残るのは区間模型から **pinchedHom への比較**、
対象 x,y の射に関する自然性、および **特徴づけの逆方向（Cor 6.2.6.5）**。
区間模型版の順方向には族の全射性・射の等式からホモトピーを得る向き・パラメータ自然性を
用いた。表示をホモトピー類での全単射と呼ぶには、別途ホモトピー不変性の確認が要る。
B2〜B5 は未完了。対象ビルド（1682 jobs）・公理監査（136 宣言、標準三公理のみ）は成功。

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
| `qcatHomFunctor_faithful` | h Fun の表示の忠実性 | 実装済み |
| `functorCellToNatTrans`・`functorCellToNatTrans_id`・`functorCellToNatTrans_comp` | 二胞体の通常の自然変換への評価と関手性 | 実装済み |
| `functorCellToNatTrans_homotopy`・`qcatCellOfHomotopy_toNatTrans` | A1c の自然変換との一致 | 実装済み |
| `QCatAdjunction.mkOfHomTriangles` | h Fun に表示した二つの三角恒等式から随伴を構成 | 実装済み |
| `bicategoryAdjunct_naturality_right`・`bicategoryAdjunct_naturality_left` | adjunct 対応の二変数の自然性（任意の双圏） | 実装済み |
| `QCatAdjunction.homEquiv_naturality_right`・`homEquiv_naturality_left` | h Fun に表示した同じ自然性 | 実装済み |
| `intervalFamily_boundary`・`intervalFamily_zero`・`intervalFamily_one` | 区間模型の固定端点の式 | 実装済み |
| `intervalFamilyCurry`・`intervalFamilyUncurry_curry` | 端点を指定した区間の族の普遍性 | 実装済み |
| `intervalFamilyHomotopy`・`intervalFamilyEdge`・`intervalFamilyOfEdge` | 区間模型の族と定値関手間の辺を相互変換 | 実装済み |
| `intervalFamilyOfEdge_edge`・`intervalFamilyEdge_ofEdge`・`intervalFamilyEdgeEquiv` | 商を取る前の二つの変換の両逆・全単射 | 実装済み |
| `intervalFamilyHom`・`intervalFamilyHom_surjective` | 区間模型の族 → h Fun の Hom と全射性（X が quasicategory） | 実装済み |
| `intervalParameterSwap` と端点・自然性・時間制限の補題 | Δ[1]×(A×B)→A×(Δ[1]×B) の座標交換 | 実装済み |
| `intervalTransposeUncurry` と端点・前合成の補題 | Fun(A,X) の区間族を X の区間族へ展開 | 実装済み |
| `intervalFamilyTranspose`・`intervalFamilyTranspose_uncurry`・`intervalFamilyTranspose_precomp` | 定値関手間の区間族 B→Map → A×B→Map(x,y) と自然性 | 実装済み |
| `rightHomotopySquareOrder`・`rightHomotopySquare` と四辺の補題 | (s,t)↦(s=0 なら t、他は 2) による正方形→三角形 | 実装済み |
| `rightHomotopyInterval`・`rightHomotopyInterval_uncurry` | CompStruct(id,f,g) から区間模型の族を作る | 実装済み |
| `rightHomotopyIntervalFamily_zero`・`rightHomotopyIntervalFamily_one` | 転置した族の時間零・一の値 | 実装済み |
| `intervalFamilyHomotopyOfRightHomotopy` | 定値関手間の右ホモトピー → 区間模型の族のホモトピー | 実装済み |
| `intervalFamilyHom_eq_imp_homotopy` | h Fun の射が等しい族はホモトピック（X が quasicategory） | 実装済み |
| `intervalFamilyHomPrecomp`・`intervalFamilyHom_precomp` | h Fun の Hom のパラメータ前合成と族の表示の自然性 | 実装済み |
| `bicategoryAdjunct_whiskerLeft` | 任意の双圏の adjunct 対応は一胞体による前合成と整合 | 実装済み |
| `qcatSSetPrecomposition`・`qcatCatHomEquiv`・`qcatCatPrecomposition` | 豊穣前合成と内部 Hom の pre、hoFunctor の単位・合成移送との比較 | 実装済み |
| `qcatCell_whiskerLeft` | QCat の二胞体の左 whisker = h(pre) による作用 | 実装済み |
| `QCatAdjunction.homEquiv_precomp` | 一般の U,V の adjunct 対応の内部 Hom 前合成に関する自然性 | 実装済み |
| `ConstantFunctorHom`・`constantFunctorCompIso` | 定値関手間の Hom、後合成での定値関手の保存の同一視 | 実装済み |
| `QCatAdjunction.constantHomEquiv` と順・逆の前合成自然性 | h Fun(A,Y)(const F(x),const y) ≃ h Fun(A,X)(const x,const G(y)) | 実装済み |
| `QCatAdjunction.intervalMap`・`intervalInverse` と `_hom` | 区間模型の比較射・逆候補と表す adjunct の仕様 | 実装済み |
| `QCatAdjunction.intervalMap_family`・`intervalInverse_family` | 任意の quasicategory パラメータ族で順・逆 adjunct を表す | 実装済み |
| `QCatAdjunction.intervalMap_unique_homotopy` | 指定された普遍族の adjunct を表す射はホモトピーまで一意 | 実装済み |
| `QCatAdjunction.intervalMap_inverse_homotopy`・`intervalInverse_map_homotopy` | 両合成から恒等射への実際の単体的ホモトピー | 実装済み |
| `QCatAdjunction.intervalMap_isSimplicialHomotopyEquivalence` | 随伴から区間模型の写像空間のホモトピー同値 | 実装済み（pinched への移行は未完了） |
| 写像空間による特徴づけ | 自然な pinchedHom のホモトピー同値との同値 | 未完了 |
| B2〜B5 | §1 の全項目 | 未着手（監査スクリプトは作成済み） |
