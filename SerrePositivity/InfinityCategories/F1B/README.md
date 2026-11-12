# F1B：随伴・Kan 拡張・cofinality・局所化

入口は [F1B.lean](../Project/Entrypoints/F1B.lean)。モジュールを役割別に配置し、宣言の型・証明は Lean ソースを正本とする。
ディレクトリと数学上の名前空間は別で、移動だけでは名前空間を変えない。

| ディレクトリ | 内容 |
|---|---|
| Adjunction | 随伴、単位・余単位、三角恒等式 |
| KanExtension | 左右 Kan 拡張、点ごとの特徴付け、普遍性 |
| NerveComparison | 通常圏の nerve と ∞ 圏の錐・Kan 拡張の比較 |
| Cofinality | cofinality、Quillen A、弱可縮性による判定 |
| Localization | 局所化と前合成による普遍性 |
| FunctorCategories | 関手 ∞ 圏、自然変換、合成とパラメータ |
| MappingSpaces | 写像空間、区間、随伴と Hom の対応 |
| Cones | 錐・余錐と図式の操作 |
| Fibrations | 相対持ち上げ、cartesian 辺と比較 |
| KanComplex | Kan 複体、弱同値、ホモトピー類 |
| Homotopy | ホモトピーと変形 |
| Diagrams | 図式と simplicial replacement の補助 |
| CocartesianScaffold | cocartesian scaffold の固有部分 |
| Joins | join の幾何と制限 |
| Equivalences | 同値の補助 |

Kan 拡張と Kan 複体の数学的な語としての Kan は残す。旧レーンに由来する `kan`／`Kan` 接頭辞の整理と、
重複側の原本への置換は [リファクタリング計画](../../../formalization-plans/refactoring-infinity.md) §5 の対応表を参照。
旧モジュールの互換シムはない。

PinchedInterval の重複6モジュールは F1/MappingSpaces の原本を使う。scaffold の共通部は
Core/SubcomplexInverseImageComparison、F1/Diagrams/ScaffoldFiberMaps、
F1/Scaffold/FinitePrism・FiniteFiberGeometry、および既存の Diagrams 原本に置く。
充填性を仮定する固有部分はそれぞれの scaffold モジュールに残す。

検証はリポジトリ直下で `scripts/refactor/verify.sh`。
F1B の公理・禁止 import 閉包は `scripts/audit_infinity_f1b.lean`、F1/F1B 間の参照は
`scripts/audit_infinity_f1_f1b.lean` で監査する。
