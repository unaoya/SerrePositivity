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
| B1 | 単位・余単位と h Fun の三角恒等式、写像空間との特徴づけ、合成、随伴関手の一意性 | Kerodon [Def 6.1.1.1](https://kerodon.net/tag/02CG)、[§6.1.3](https://kerodon.net/tag/02D5)、[§6.1.5](https://kerodon.net/tag/02DM)、[Def 6.2.1.1・Prop 6.2.1.17](https://kerodon.net/tag/02EJ)、[Prop 6.2.6.1](https://kerodon.net/tag/02FV)・[Cor 6.2.6.5](https://kerodon.net/tag/02FX) / HTT §5.2 |
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
ことも証明した。これは **任意の固定端点の写像空間同値から Hom 対応への橋** である。

逆方向の代数的な終点を実装した。`BicategoryHomCorrespondence` は任意の双圏での
Hom 全単射、二変数自然性、パラメータの左 whisker との整合を持つ。恒等関手の
単位子の像・逆像から単位・余単位を取り出し、三角恒等式をこれらの自然性から導出した。
`adjunctionEquiv` は自然な対応と随伴のデータの全単射で、両方向の往復を証明している。
`QCatFunctorHomCorrespondence` は任意の関手 U:A→X、V:A→Y の h Fun の Hom と
内部 Hom の前後合成・パラメータ前合成で同じ条件を表示する。この型から
`QCatAdjunction` を構成し、元の Hom 対応・単位・余単位を回収する公式を得た。
三角恒等式や随伴の存在を対応の入力に含めていない。
さらに、指定された単位による canonical な二胞体の Hom 写像の全単射性から、
その単位を持つ随伴を構成する判定を双圏と h Fun の表示で実装した。
**この判定の全単射条件は全ての quasicategory パラメータ A と任意の U,V に課す。**
点ごとの hX の Hom 全単射に弱めていない。

非定値の関手 U,V の区間写像空間の族を、A×B 上の端点 fst≫U,fst≫V の
ホモトピーへ展開する `transformationFamilyEquiv` を実装した。curry と uncurry は
ホモトピー類を取る前に厳密に両逆で、関手の変数 A の制限、族の変数 B の前合成、
標的の後合成との自然性を証明した。以前の定値端点 x,y の転置とは別に、U,V 自体を保つ。
さらに Fun(A,X) を周囲の quasicategory として、pinched 写像空間の比較を π₀ 経由で
直接 h Fun の Hom に移す `functorMappingSpaceHomEquiv` を構成した。
比較の合成・恒等・ホモトピー可換正方形は Hom の等式に移り、特に内部 Hom の前合成との
自然性ホモトピーから `QCatFunctorHomCorrespondence.precomp` の形の等式を導いた。
この橋は U,V を定値関手に置き換えない。
`qcatAdjunctionOfUnitMappingEquivalences` は **全ての A と任意の U,V** で単位を表す
pinched 写像空間のホモトピー同値が与えられた場合に、指定単位を持つ随伴を構成する。
単位の公式との整合は全ての代表辺（pinched の零単体）で照合し、Hom 全単射性は
写像空間の同値から導く。余単位・三角恒等式・随伴の存在は入力しない。

指定単位による各点の比較の公式も実装した。`qcatUnitHomMap_formula` は任意の η について
単位比較を h(pre U)(η) と G による後合成の合成で表示する。単位の普遍性は仮定せず、
終域側の合成とパラメータ前合成との自然性を得た。`functorHomEvaluate` は h Fun の二胞体を
各頂点で評価し、その定値族が定値射による前合成に一致することを端点の輸送込みで示した。
これにより `constantUnitHomMap_formula` は定値関手間の単位比較を、各点の単位成分の
定値族と G の作用によって表示する。
`unitIntervalMap η x y` は G の作用の後に `qcatUnitComponent η x` で前合成する実際の射で、
任意の quasicategory パラメータの族の Hom 表示が上の単位比較に一致する。
pinched 模型へ移した `unitPinchedMap` は、**pinchedHomMap G の後に単位成分で前合成する**
射と厳密に等しい（`unitPinchedMap_formula`）。随伴の単位に対しては、これらの標準比較と
既存の adjunct 比較との実際のホモトピー・h Fun の同型を構成し、同値性を得た。
`UnitMappingSpaceCondition η` は **各点 x,y だけ** の標準 pinched 比較のホモトピー同値性を
述べる型であり、全パラメータ A の条件を定義に追加しない。区間模型の標準比較による
条件との同値も証明した。随伴からこの条件への順方向（Cor 6.2.6.5 の (1)⇒(2)）は実装済み。

局所存在のための comma の図式を構成した。`unitComma G` は区間の境界制限を
`X×Y → Fun(∂Δ[1],X)` に引き戻した単体集合で、矢印 x→G(y) の coherent な族を保持する。
端点の組と始域への射影は inner fibration、X,Y が quasicategory なら全体と固定始域の
fiber も quasicategory である。ここで用いる直積の第一射影の inner fibration 性も F1B 内で証明した。
`functorHomHomotopy` は非可逆な二胞体の実際のホモトピー代表を選び、元の二胞体と各点の
評価を回収する。この代表によって `unitCommaSection η` を構成し、始域への厳密な切断であり、
標的関手が指定された F であることを証明した。
`universalUnitComma G` は、自身の始域の fiber 内で始対象である頂点が張る全部分単体集合。
`UnitCommaInitialCondition η` は単位の成分がその頂点条件を満たすことを述べ、指定した x 上の
`unitCommaSectionVertex η x` の始対象性との同値も証明した。この中間条件の下で単位の切断を
普遍矢印へ制限し、始域射影の inner fibration 性・頂点上の全射性と標的関手 F の回収を得た。
**これだけから射影の同値性を主張しない。** 充満忠実性または外側ホーンを含む相対充填が残る。
固定始域の comma の任意の族を、Y 値の図式 b とホモトピー `const x → G∘b` の
組へ展開する厳密な全単射 `unitCommaFiberFamilyEquiv` を構成した。パラメータの前合成に
関する標的・ホモトピーの公式と、両データによる射の外延性も証明済みである。
`unitCommaFiber_exists_extension_iff` は任意の射 i に沿う fiber 内の延長問題を、
b とホモトピーの同時延長へ厳密に移す。`unitCommaFiber_isInitialVertex_iff` により、
始対象性を初頂点を指定した境界図式とホモトピーの同時延長で判定できる。
これは元の始対象性との同値であり、各点の写像空間条件から延長が存在する証明はまだ残る。
原典 Prop 6.2.6.1 の証明は relative join の cartesian fibration を使う。現在の境界引き戻しの
区間 comma 模型について、その cartesian な輸送や原典模型との比較はまだ実装していない。

始対象性について、`isInitialVertex_iff_pinchedHomLeft_isContractibleKan` を実装した。
可縮性の反転不変性を境界充填から証明し、Core の終対象の右模型での判定と
Stable の `InitialOpposite` の双対化を読み取り専用で利用する。依存は狭いモジュールに限定する。
`UnitCommaFiberSquare` は Y の区間図式と X のホモトピーを持ち、両側辺を指定頂点の
comma 矢印に固定する。`unitCommaFiberMappingSquareEquiv` は任意のパラメータ A について、
comma fiber の**区間**写像空間の族と正方形との厳密な全単射を与える。
標的図式は comma の標的射影による実際の写像空間の作用と整合する。

`unitCommaInitialCondition_iff_mappingSpaces` は単位の comma 始対象条件を各 fiber の
**左 pinched** 写像空間の可縮性に書き換える。一方 `unitIntervalComparisonFiber` は標準単位比較の
可逆 path 置換の fiber であり、`UnitMappingSpaceCondition` から全ての指定点での可縮性を証明した。
**元の比較射の strict fiber が可縮だとは主張しない。** 区間の族の反転と逆反転の
厳密な両逆・パラメータ自然性を構成し、境界と標準単体の反転同型によって区間模型の可縮性の
反転不変性を証明した。これと反転標的での右 pinched 比較により、
`isInitialVertex_iff_intervalMappingSpace_isContractibleKan` と、単位に特殊化した
`unitCommaInitialCondition_iff_intervalMappingSpaces` が得られる。既存 F1 の左模型比較には
`LeftUnstraightening` が推移的に含まれるため、それを import せず、この経路を用いる。
comma の始対象判定と正方形表示は、これで同じ区間模型上にそろった。
`homMk_comp_eq_of_square` は任意の四辺の正方形の二つの合成を h で同定し、
単位比較の導来 fiber への射に必要な合成関係を与える一般補題である。
comma の正方形を Fun(A,X) へ curry し、四辺の厳密な計算から、左辺と G の標的辺の合成が
右辺になることを証明した。左辺が指定単位の成分の定値族であることも、選んだ代表の射と
h Fun の類の両方で照合済み。右辺の族は `unitCommaArrowVertex` への定値射である。
`unitCommaSquareTargetFamily_unit_homotopy` は、標的族の標準単位比較の像から右辺の族への
実際のホモトピーを与える（パラメータ A の quasicategory 性や単位比較の同値性を仮定しない）。
これを普遍正方形へ適用し、可逆 path への curry と fiber の持ち上げを使って
`unitCommaMappingToComparisonFiber` を構成した。元の始域の写像空間への射影は、正方形の
標的族に厳密に一致する。
逆向きの基準図式として `unitIntervalCompositionTriangle` を構成した。パラメータは
Map(F(x),y) 全体で、元の単位の代表、G による普遍標的辺、標準単位比較の普遍族を
指定三辺に持つ実際の三角形である。`FunctorCompositionTriangle.precomp` と
`unitIntervalCompositionTriangle_family` は、この一つの基準三角形を任意の族へ制限する。
族ごとに独立に三角形を選び直さず、図式は基準図式への前合成そのものとなる。
`exists_functorDiagramPath_lift_relative` は単射に沿う図式制限の可逆 path を、既定の部分族と
始点の図式を保って持ち上げる。制限後の path 自体を厳密に保持する。
三角形の境界を合成ホーンと対角辺の pushout として表示し、重なり上の一致を二端点だけで
判定できる `triangleBoundaryDiagram` を構成した。三面の制限は全て厳密に回収する。
`intervalFamilyPath` は区間族のホモトピーを、関手正方形の交換と curry によって矢印を動かす
可逆 path の図式へ移す。始域・標的の頂点での縦 path は定値で、時間の始点・終点も
それぞれ元の族の矢印表示に一致する。この変換には X の quasicategory 性も不要。
`unitCompositionBoundaryPath` は標準単位比較の像から指定族へのホモトピーを、基準合成三角形の
境界全体の可逆 path に組み込む。二つの合成辺を固定し、対角辺で与えられた path 自体を厳密に
回収する。境界 path の始点は基準三角形の境界に厳密に一致する。
残る接続は、境界 path を関手単体集合内の path へ移し、相対持ち上げを適用して三角形を運び、
逆向きの比較と両合成のホモトピーを構成する部分である。合成の Hom の等式から三角形を
族ごとに選ぶだけでは、与えられた path の情報を保つ保証はない。
**比較射の逆射・両合成のホモトピーと同値性は未証明。** 順方向の射と終域の可縮性だけでは
始域の可縮性は従わず、始対象性を結論してはならない。

B1 の逆方向全体は未完了。残るのは、自然な各点の pinched 写像空間対応から単位を取り出す
接続と、`UnitMappingSpaceCondition η` から
`∃ a : QCatAdjunction F G, a.unitHom = η` を構成する逆方向である。
comma の経路では、各点の比較の同値性から `UnitCommaInitialCondition η` を導き、普遍矢印の
射影の充填・輸送を使って自然な余単位と三角恒等式へ接続する必要がある。
既存の全パラメータ版の経路も利用できるが、その十分条件で原典の各点の条件を置き換えて
B1 完了とはしない。B2〜B5 も未完了。
対象ビルド（2023 jobs）・公理監査（800 宣言、標準三公理のみ）は成功。
推移的 import のリポジトリ内 355 モジュールに straightening 依存がないことも確認した。

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
| `BicategoryHomCorrespondence` | 全パラメータの二胞体の Hom 全単射と二変数・左 whisker 自然性 | 実装済み |
| `BicategoryHomCorrespondence.unit/counit`・`left_triangle/right_triangle` | 恒等関手の単位子から単位・余単位を構成し、自然性から三角式を導出 | 実装済み |
| `BicategoryHomCorrespondence.toAdjunction/ofAdjunction`・`adjunctionEquiv` | 自然な Hom 対応と双圏随伴の全単射、両方向の回収 | 実装済み |
| `FunctorHom`・`QCatFunctorHomCorrespondence` | 任意の関手 U,V の h Fun の Hom を使った自然な対応の表示 | 実装済み |
| `QCatFunctorHomCorrespondence.toBicategory/toAdjunction`・`adjunctionEquiv` | h Fun の自然な対応から QCat 随伴を構成し、両方向の回収を証明 | 実装済み |
| `QCatFunctorHomCorrespondence.toAdjunction_homEquiv/unitHom/counitHom` | 構成した随伴の対応・単位・余単位の明示的な仕様 | 実装済み |
| `bicategoryUnitHomMap` と三つの自然性 | 任意の単位候補からの canonical な二胞体の Hom 写像 | 実装済み |
| `BicategoryHomCorrespondence.ofUnit`・`bicategoryAdjunctionOfUnitHomBijective` | 全パラメータの単位 Hom 写像の全単射性から随伴を構成 | 実装済み |
| `bicategory_exists_adjunction_unit_iff` | 指定単位を持つ双圏随伴と全パラメータ Hom 全単射条件の同値 | 実装済み |
| `qcatUnitHomMap`・`qcatAdjunctionOfUnitHomBijective`・`qcat_exists_adjunction_unitHom_iff` | h Fun の指定単位と全パラメータ Hom 全単射による同じ判定 | 実装済み |
| `transformationFamilyUncurry`・`transformationFamilyHomotopy` と端点公式 | 非定値 U,V の写像空間の B 族を A×B 上のホモトピーへ展開 | 実装済み |
| `transformationFamilyCurry`・`transformationFamilyEquiv` | 展開の厳密な逆とホモトピー類を取る前の全単射 | 実装済み |
| `transformationFamilyUncurry_precomp/restrict/postcomp`・`transformationFamilyHomotopy_precomp/restrict/postcomp` | B の前合成・A の制限・標的後合成との自然性 | 実装済み |
| `mappingSpaceHomMap`・`mappingSpaceHomMap_bijective`・`mappingSpaceHomEquiv` | pinched 比較から直接周囲の h 圏の Hom に移す射・全単射 | 実装済み |
| `mappingSpaceHomMap_homMk`・`mappingSpaceHomMap_eq_of_homMk`・`mappingSpaceHomMap_eq_of_homotopy` | 代表辺での計算と認識、ホモトピー不変性 | 実装済み |
| `mappingSpaceHomMap_functor/comp/id/square` | 関手の作用・合成・恒等・ホモトピー可換正方形の移送 | 実装済み |
| `functorMappingSpaceHomEquiv`・`functorMappingSpaceHomEquiv_precomp` | 非定値関手間の写像空間比較から Hom 全単射とパラメータ自然性を導く | 実装済み |
| `qcatUnitHomMap_bijective_of_mappingSpace` | 代表辺で単位を表す写像空間比較の同値性から Hom 全単射を導く | 実装済み |
| `qcatAdjunctionOfUnitMappingEquivalences`・`qcatAdjunctionOfUnitMappingEquivalences_unitHom` | 全 A,U,V の比較から指定単位を持つ随伴を構成（各点の条件への還元は未完了） | 実装済み |
| `qcatUnitHomMap_formula`・`qcatUnitHomMap_naturality_right/precomp` | 任意の単位候補による比較の内部 Hom での公式と自然性 | 実装済み |
| `evaluateFunctorAt_constantFunctorMap`・`functorHomEvaluate` と恒等・合成・定値族の公式 | 点での評価と定値射による前合成の同一視 | 実装済み |
| `homMk_transport`・`intervalFunctorMap_familyHom` | 辺の端点の輸送と、族の後合成の h Fun の表示 | 実装済み |
| `qcatUnitComponent`・`constantUnitHomMap` と `_formula`・`_of_adjunction` | 単位の各点成分と定値関手間の比較、既存の adjunct との一致 | 実装済み |
| `unitIntervalMap`・`unitIntervalMap_family` | G の作用の後に単位成分で前合成する標準比較と任意の族での公式 | 実装済み |
| `QCatAdjunction.unitIntervalMap_homotopy`・`unitIntervalMap_isSimplicialHomotopyEquivalence` | 随伴の単位による標準比較と既存の adjunct 比較の実際のホモトピー、同値性 | 実装済み |
| `unitPinchedMap`・`unitPinchedMap_formula`・`QCatAdjunction.unitPinchedMapIso` | pinched 模型の標準単位比較、原典の合成の公式、既存の adjunct との同型 | 実装済み |
| `UnitMappingSpaceCondition`・`unitMappingSpaceCondition_iff_interval` | 全 x,y のみの標準比較の同値条件、模型独立性 | 実装済み |
| `QCatAdjunction.unitMappingSpaceCondition` | 随伴の単位は各点の標準比較の同値条件を満たす（Cor 6.2.6.5 (1)⇒(2)） | 実装済み |
| `functorHomHomotopy`・`functorHomHomotopy_hom`・`functorHomHomotopy_component` | 任意の二胞体の実際の代表と、類・各点の評価の回収 | 実装済み |
| `innerFibration_productFst` | 第二因子が quasicategory である直積の第一射影は inner fibration | 実装済み |
| `unitCommaBoundary`・`unitComma`・`unitCommaArrow/Pair/Source/Target` | x→G(y) の区間 comma とその射影 | 実装済み |
| `unitCommaPair_innerFibration`・`unitCommaSource_innerFibration`・`unitComma_quasicategory` | 端点の組・始域の射影の充填性と全体の quasicategory 性 | 実装済み |
| `unitCommaLift` と矢印・端点・始域・標的の公式 | a→G∘b のホモトピーから comma 値の図式を構成 | 実装済み |
| `unitCommaSection`・`unitCommaSection_source/target` | 指定単位による厳密な切断、標的 F の回収 | 実装済み |
| `unitCommaFiber`・`unitCommaFiber_quasicategory`・`unitCommaSectionVertex` | 固定始域の fiber と単位の成分の頂点 | 実装済み |
| `IsUniversalUnitCommaVertex`・`universalUnitComma`・`UnitCommaInitialCondition` | fiber 内の始対象条件とその頂点が張る全部分単体集合 | 実装済み |
| `unitCommaInitialCondition_iff` | 始対象条件を指定した x 上の単位の頂点で表示 | 実装済み |
| `universalUnitCommaProjection_innerFibration`・`universalUnitCommaSection` と射影・標的の公式 | 中間始対象条件の下での普遍矢印への切断と inner fibration 性 | 実装済み |
| `universalUnitCommaProjection_surjective` | 同じ条件の下での始域射影の頂点上全射性（同値性は未証明） | 実装済み |
| 写像空間による特徴づけ | 自然な pinchedHom のホモトピー同値との同値 | 未完了 |
| B2〜B5 | §1 の全項目 | 未着手（監査スクリプトは作成済み） |
| `unitCommaUncurry`・`unitCommaHomotopy`・`unitCommaLift_homotopy` | comma の族の展開と厳密な回収 | 実装済み |
| `unitCommaFiberCurry`・`unitCommaFiberFamilyEquiv` | 固定始域の族と標的図式・ホモトピーの組の厳密な全単射 | 実装済み |
| `unitCommaFiberTarget_precomp`・`unitCommaFiberHomotopy_precomp`・`unitCommaFiber_hom_ext` | パラメータ自然性と二データによる外延性 | 実装済み |
| `unitCommaFiber_exists_extension_iff` | 任意の射に沿う延長問題と図式・ホモトピーの同時延長の同値 | 実装済み |
| `unitCommaFiber_isInitialVertex_iff` | 初頂点固定の境界延長による始対象性の判定 | 実装済み |
| `isContractibleKan_of_op`・`IsContractibleKan.op`・`isContractibleKan_op_iff` | 境界充填による可縮性の反転不変性 | 実装済み |
| `IsInitialVertex.pinchedHomLeft_isContractibleKan`・`isInitialVertex_iff_pinchedHomLeft_isContractibleKan` | 始対象性と全ての左 pinched 写像空間の可縮性の同値 | 実装済み |
| `unitCommaFiber_precomp_eq_iff` | comma fiber の制限の等式を標的とホモトピーで判定 | 実装済み |
| `UnitCommaFiberSquare`・`unitCommaFiberMappingSquareEquiv` | comma fiber の区間写像空間の族を側辺固定の正方形で表示 | 実装済み |
| `unitCommaFiberMappingSquare_target` | 正方形の標的と標的射影の写像空間上の作用の整合性 | 実装済み |
| `unitCommaInitialCondition_iff_mappingSpaces` | 単位の始対象条件の左写像空間での表示 | 実装済み |
| `unitIntervalComparisonFiber`・`UnitMappingSpaceCondition.unitIntervalComparisonFiber_isContractibleKan` | 標準単位比較の導来 fiber と各点条件による可縮性 | 実装済み |
| `intervalReverseFamily`・`intervalUnreverseFamily` と両逆・前合成の公式 | 反転パラメータ付き区間族の厳密な対応 | 実装済み |
| `intervalMappingSpace_op_isContractibleKan_iff` | 境界充填による区間写像空間の可縮性の反転不変性 | 実装済み |
| `isInitialVertex_iff_intervalMappingSpace_isContractibleKan` | 出る区間写像空間の可縮性による始対象判定 | 実装済み |
| `unitCommaInitialCondition_iff_intervalMappingSpaces` | 正方形表示と同じ区間模型での単位の始対象条件 | 実装済み |
| `homMk_comp_eq_of_square` | 任意の四辺の正方形の二つの合成の h での等式 | 実装済み |
| `functorHom_comp_eq_of_square`・`UnitCommaFiberSquare.functorSquare` と四辺の公式・`hom_comp` | comma の coherence による h Fun の合成関係 | 実装済み |
| `unitCommaSectionVertex_homotopy_const`・`unitCommaSectionVertexHomotopy_hom` | comma の左辺と指定単位の代表・類の照合 | 実装済み |
| `unitCommaVertexHomotopy`・`unitCommaArrowFamily`・`unitCommaArrowVertex`・`unitCommaArrowFamily_eq_const` | 右辺の矢印の区間表示と定値性 | 実装済み |
| `unitCommaSquareTargetFamily`・`unitCommaSquareTargetFamily_unit_homotopy` | 正規化した標的族と標準単位比較の像から右辺への実際のホモトピー | 実装済み |
| `homotopyEquivalencePath`・`homotopyPathReplacementLift` と射影・終点の公式 | Kan 複体内のホモトピーによる可逆 path 置換への持ち上げ | 実装済み |
| `unitCommaMappingToComparisonFiber`・`unitCommaMappingToComparisonFiber_projection` | comma の区間写像空間から単位比較の導来 fiber への順方向の射、底との整合性 | 実装済み（同値性は未証明） |
| `FunctorCompositionTriangle`・`nonempty_functorCompositionTriangle_of_homEq` | 指定三辺の代表を持つ実際の合成三角形 | 実装済み |
| `FunctorCompositionTriangle.precomp` | 基準三角形のパラメータ制限、三辺の raw な前合成を保持 | 実装済み |
| `unitIntervalCompositionTriangle`・`unitIntervalCompositionTriangle_family` と図式の公式 | 標準単位比較の基準合成三角形と任意の族への制限 | 実装済み |
| `exists_functorDiagramPath_lift_relative` | 単射に沿う図式の可逆 path の相対持ち上げ、部分族・始点・制限後の path を保持 | 実装済み |
| `triangleBoundary_bicartSq`・`triangleBoundary_isPushout`・`triangleDiagonalEndpoints_hom_ext` | 合成ホーンと対角辺による境界の pushout、重なりの二端点による判定 | 実装済み |
| `triangleBoundaryDiagram` と三面の制限公式 | 指定された二辺と対角辺の図式を厳密に貼り合わせる | 実装済み |
| `triangleBoundaryPath`・`triangleBoundaryPath_start` | 固定した二辺と動く対角辺の境界の path、始点の境界を回収 | 実装済み |
| `intervalFamilyPath` と始点・終点・頂点の公式 | 区間族のホモトピーから矢印を動かす可逆 path の図式への変換 | 実装済み |
| `unitCompositionBoundaryPath`・`unitCompositionBoundaryPath_diagonal/start` | 単位比較の像を動かすホモトピーを合成三角形の境界へ組み込む、実際の path と始点を保持 | 実装済み |
