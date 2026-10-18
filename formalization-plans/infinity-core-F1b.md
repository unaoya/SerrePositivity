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
  右模型の比較は `F1B/PinchedInterval*.lean` の `PinchedInterval` namespace に置く。
  相対 join 延長・端点固定の持ち上げ・レトラクションの一般補題は、straightening に
  依存しない F1 の小さいモジュールから読む。共有の F1/ は編集しない。
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

右 pinched 模型→区間模型の比較を、任意の族の回収、厳密な左逆、ホモトピー右逆から
証明した。この模型比較を前後で合成した `pinchedHomEquivalence` は
`pinchedHom(F(x),y)` と `pinchedHom(x,G(y))` の明示的な同値で、順射 `pinchedMap` は
実際の単体的ホモトピー逆を持つ。区間模型の adjunct 比較との h Fun の同型による整合も公開した。
模型比較そのものは、任意の単体集合の射の作用と厳密に可換である。

定値関手への単体的な射 `constantFunctorMap` と h の射への作用を構成した。
恒等・合成・パラメータ前合成・標的の関手による後合成との整合を証明し、
右 whisker と内部 Hom の後合成を比較した。これにより `constantHomEquiv` の
対象変数の hX・hY の任意の射に関する二変数自然性を証明した。
区間写像空間への前後合成作用を、普遍族の h Fun での合成を代表する実際の射として構成し、
任意の単体集合パラメータでの公式と、恒等・合成・前後合成の交換の実際のホモトピーを得た。
`intervalMap_naturality_left/right` は随伴比較がこれらの作用とホモトピーまで可換であることを述べる。
pinched 模型では、比較による移送 `PinchedInterval.liftMap` の合成整合を使い、
同じ前後合成作用とその恒等・合成・交換の同型を構成した。既存の `pinchedMap` がこの移送と
等しいことを確認し、`pinchedMap_naturality_left/right` を実際のホモトピーとして公開した。

これは B1 全体の完了ではない。**特徴づけの逆方向（Cor 6.2.6.5）** が残る。
上の自然性は hX・hY の射と任意のパラメータの h Fun での対応として検証した段階であり、
逆向きに入力する自然な写像空間対応の型と、そこから単位・余単位を構成する接続は未実装。
Cor 6.2.6.5 は指定された自然変換 η が誘導する比較の同値性を使う。各点で任意に選んだ
同値だけから逆向きを主張しない。

族の表示のホモトピー不変性を証明した。`intervalFamilyHom_eq_iff_homotopy` は
h Fun の射の等式と、族の間の実際の単体的ホモトピーの存在が同値であることを述べる。
不変性の向きには X の quasicategory 性すら不要で、固定された両側の辺が退化する正方形の
二つの三角形の合成関係だけで証明した。これにより族のホモトピー類の商を取り、
`intervalFamilyHomotopyEquiv` として定値関手間の h Fun の Hom との全単射を公開した。
任意の単体集合パラメータの前合成との自然性も証明した。
さらに、区間・pinched 模型の写像空間の指定された同値から、任意のパラメータ上の
定値関手間 Hom の全単射を構成した。順射がホモトピックならこの対応は同一であり、
同値の逆や模型比較の逆の選択に由来する任意性を相殺できる。
随伴から作った区間・pinched の同値について、この橋が元の `constantHomEquiv` を回収する
ことも証明した。これは **任意の固定端点の写像空間同値から Hom 対応への橋** であり、
任意の自然な写像空間対応から h Fun の単位・余単位と三角恒等式を構成する逆方向全体は
依然として未実装。B2〜B5 も未完了。
対象ビルド（1953 jobs）・公理監査（319 宣言、標準三公理のみ）は成功。
推移的 import のリポジトリ内 285 モジュールに straightening 依存がないことも確認した。

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
| `QCatAdjunction.intervalMap_isSimplicialHomotopyEquivalence` | 随伴から区間模型の写像空間のホモトピー同値 | 実装済み |
| `PinchedInterval.comparison`・`comparison_uncurry`・`comparison_mono` | 右 pinched 模型→区間模型の指定射、任意族での公式、単射性 | 実装済み |
| `PinchedInterval.rightIntervalFatDiagram` と円柱・端点・自然性の補題 | 区間族を両端固定の fat join 図式へ展開 | 実装済み |
| `PinchedInterval.intervalMappingHomotopyOfSquare`・`intervalMappingHomotopyOfFatJoin` | 両端固定の図式のホモトピーを区間族へ戻す | 実装済み |
| `PinchedInterval.comparison_exists_homotopy`・`comparison_exists_homotopy_section` | 任意の区間族のホモトピーまでの回収と恒等族の回収 | 実装済み |
| `PinchedInterval.comparison_exists_retraction`・`comparison_isQCatEquivalence` | 相対延長による厳密な左逆と右模型の比較の同値性 | 実装済み |
| `QCatAdjunction.intervalMappingEquivalence`・`pinchedHomEquivalence` | 区間模型の同値を pinchedHom(F(x),y) と pinchedHom(x,G(y)) へ移す | 実装済み（各点でのデータ） |
| `QCatAdjunction.pinchedMap`・`pinchedMap_isSimplicialHomotopyEquivalence` | 指定した順射と実際の単体的ホモトピー逆の存在 | 実装済み |
| `QCatAdjunction.pinchedMap_comparisonIso` | pinched の順射と区間模型の adjunct 比較の h Fun での整合 | 実装済み |
| `intervalFunctorMap`・`intervalFunctorMap_uncurry` | 関手の区間模型への作用と任意族での後合成公式 | 実装済み |
| `pinchedIntervalComparison_naturality` | 模型比較は任意の単体集合の射の作用と厳密に可換 | 実装済み |
| `qcatSSetPostcomposition`・`qcatCatPostcomposition`・`qcatCell_whiskerRight` | 豊穣後合成と内部 Hom の作用、二胞体の右 whisker の一致 | 実装済み |
| `constantFunctorMap` と頂点・前後合成の公式 | X→Fun(A,X) の定値関手への射 | 実装済み |
| `constantFunctorHomMap` と恒等・合成・前後合成の公式 | hX の射を定値関手間の h Fun の射へ移す | 実装済み |
| `QCatAdjunction.homEquiv_comp_left/right` | 任意の h Fun の射について adjunct の二変数自然性を表示 | 実装済み |
| `QCatAdjunction.constantHomEquiv_naturality_left/right` | 定値関手の adjunct の hX・hY の射に関する自然性 | 実装済み |
| `intervalPrecompose`・`intervalPostcompose` と `_hom`・`_family` | hX の射による写像空間の実際の前後合成射と任意パラメータ族の公式 | 実装済み |
| `intervalPrecompose_id/comp`・`intervalPostcompose_id/comp`・`intervalPrecompose_postcompose` | 恒等・合成・前後合成交換の実際のホモトピー | 実装済み |
| `QCatAdjunction.intervalMap_naturality_left/right` | 区間模型の比較と前後合成の正方形の実際のホモトピー | 実装済み |
| `PinchedInterval.liftMap`・`liftMapCompIso`・`liftMapIso`・`liftMapIdIso`・`liftMapComparisonIso` | 模型比較による射の移送、合成・同型・恒等・比較との整合 | 実装済み |
| `PinchedInterval.precompose/postcompose` と恒等・合成・交換の同型 | pinched 模型の前後合成作用 | 実装済み |
| `QCatAdjunction.pinchedMap_eq_liftMap` | 既存の比較射と区間模型からの移送の一致 | 実装済み |
| `QCatAdjunction.pinchedMapNaturalityLeftIso/RightIso`・`pinchedMap_naturality_left/right` | pinched 比較の対象自然性の h Fun の同型と実際のホモトピー | 実装済み |
| `homMk_eq_of_square` | 両側が退化辺の正方形の横辺は h で同じ射（quasicategory 性不要） | 実装済み |
| `intervalFamilySquare` と四辺の公式 | 族のホモトピーを h Fun の二重区間の正方形へ展開 | 実装済み |
| `intervalFamilyHom_eq_of_homotopy`・`intervalFamilyHom_eq_iff_homotopy` | 族の Hom 表示のホモトピー不変性とホモトピー回収との同値 | 実装済み |
| `intervalFamilyHomotopySetoid`・`IntervalFamilyHomotopyClass` | 実際の単体的ホモトピーの存在による同値関係と商 | 実装済み |
| `intervalFamilyClassHom`・`intervalFamilyClassHom_bijective`・`intervalFamilyHomotopyEquiv` | 族のホモトピー類と定値関手間の h Fun の Hom の全単射 | 実装済み |
| `intervalFamilyClassPrecomp`・`intervalFamilyHomotopyEquiv_precomp` | 族の類の前合成と表示全単射のパラメータ自然性 | 実装済み |
| `intervalFamilyClassMap`・`intervalFamilyClassEquiv` | 写像空間の射・同値をパラメータ族の類へ移す | 実装済み |
| `intervalMappingEquivalenceHomEquiv` と族・前合成・ホモトピー不変性の公式 | 区間写像空間の同値からパラメータに自然な Hom 全単射を得る | 実装済み |
| `intervalEquivalenceOfPinched`・`pinchedMappingEquivalenceHomEquiv`・`pinchedMappingEquivalenceHomEquiv_precomp` | pinched 同値を区間模型経由で同じ Hom 全単射へ移す | 実装済み |
| `QCatAdjunction.intervalMappingEquivalence_homEquiv`・`pinchedHomEquivalence_homEquiv` | 随伴が与える区間・pinched 同値から元の adjunct 対応を回収 | 実装済み |
| `QCatAdjunction.pinchedEquivalenceIntervalIso` | 随伴の pinched 比較を区間模型に戻すと元の比較射に同型 | 実装済み |
| 写像空間による特徴づけ | 自然な pinchedHom のホモトピー同値との同値 | 未完了 |
| B2〜B5 | §1 の全項目 | 未着手（監査スクリプトは作成済み） |
