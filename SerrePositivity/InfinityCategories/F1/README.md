# F1 の規約

概要：fibration・straightening・Yoneda の実装を配置する。
方針：`formalization-plans/archive/stage-i/infinity-lanes/infinity-core-F1.md` §1 の順に進める。
規約：namespace は `SerrePositivity.InfinityCategories`。Core・Coherent・DGNerve・Derived は参照のみ。
使われ方：Kerodon 第 5・6・7.3・8 章に対応する一般論。

## F1a：辺と fibration

Kerodon Definition 5.1.1.1 に従い、辺は一単体として表す。
cartesian 辺では最後の辺を固定した最後の外側ホーン、cocartesian 辺では最初の辺を
固定した零番目の外側ホーンの相対持ち上げ性を要求する。次元は `n + 2` とする。

Kerodon Definition 5.1.4.1 に従い、fibration は内ホーンの `MorphismProperty.rlp` と
指定端点からの cartesian/cocartesian 辺の存在を組み合わせる。
持ち上げの選択は構造に含めない。底の quasicategory 性は定義に含めない。
`Core/RightFibration.lean` の right/left fibration はそれぞれ cartesian/cocartesian
fibration に接続する。底変換の射は `pullback.snd p q` とする。

## 後続工程の境界

F1d 着手前に Kerodon 5.3〜5.6 を照合し、left fibration・𝒮 値の場合を先に完成させる
文言と証明方針を本書に記録・報告する。
𝒮 と Cat_∞ は γ1 の coherent nerve を用いる。その極限・余極限は F2 の担当とする。

## F1d：着手前の原典照合と証明方針（2026-10-18）

概要：left fibration と 𝒮 値関手の分類・straightening を先に完成させ、その後に
cocartesian fibration と Cat_∞ 値関手へ拡張する。
方針：coherent nerve、相対関手単体集合、ホーン充填、weighted nerve と scaffold の
組み合わせ論で構成と比較を証明する。
規約：𝒮 は `SpaceInfinity = N^hc(KanObject)`、Cat_∞ は `CatInfinity = N^hc(QCat)`。
両者の quasicategory 性は `Coherent/Quasicategory.lean` の γ1 を用いる。
使われ方：Kerodon §§5.3–5.6、特に Theorem 5.6.0.2 と Corollary 5.6.0.6。

### 照合した文言

| 原典 | 本レーンでの扱い |
| --- | --- |
| [§5.3](https://kerodon.net/tag/035A)、[Construction 5.3.1.5](https://kerodon.net/tag/035J) | 現行 §5.3 は通常の圏の nerve 上の fibration。strict transport は各 undercategory の nerve 上の cocartesian な持ち上げを集めた相対関手単体集合であり、任意に選んだ辺の transport を厳密に合成する構成ではない。 |
| [Definition 5.3.3.1](https://kerodon.net/tag/025X)、[Theorem 5.3.5.6](https://kerodon.net/tag/037P) | weighted nerve と scaffold によって strict diagram を fibration と比較する。定理の結論は同値類の全単射。 |
| [§5.4](https://kerodon.net/tag/01W4) | 現行 §5.4 は ∞-bicategory の一般論。これを新たな基盤として導入する経路は採らず、後述の相対的な比較と延長を quasicategory の充填で別途証明する。原典の結論を無証明で引き継がない。 |
| [§5.5](https://kerodon.net/tag/01YV)、[§5.5.2](https://kerodon.net/tag/01ZV) | 𝒮 の Δ⁰ からの coslice と射影を使う。射影は left fibration。fiber と元の Kan 複体との比較は一般に同型ではなく同値なので、比較を別に証明する。 |
| [Theorem 5.6.0.2](https://kerodon.net/tag/028K)、[Corollary 5.6.0.6](https://kerodon.net/tag/028T) | 前者は Cat_∞ 値関手の関手同型類と essentially small cocartesian fibrations の同値類の全単射、後者は 𝒮 値・left fibration 版。対象の分類だけから関手 ∞ 圏の同値が得られたとは扱わない。 |
| [Theorem 5.6.5.12](https://kerodon.net/tag/0293)、[Corollary 5.6.5.15](https://kerodon.net/tag/0296) | 相対表現の延長が存在と一意性の要点。境界を固定した表現の延長とパラメーター付きの比較を、実装上の証明課題として残さず解く。 |

### 実装順と証明課題

1. 𝒮 の Δ⁰ を指定する頂点と、その coslice `PointedSpaceInfinity → SpaceInfinity`
   を構成する。任意の coherent diagram `F : C → SpaceInfinity` に沿う引き戻しを
   unstraightening の候補とし、left fibration 性と底変換を直接証明する。
2. coherent nerve の Hom と既存の写像空間を比較し、候補の fiber が `F(c)` を表す
   Kan 複体と自然に同値であることを証明する。fiber の厳密な等式を前提にしない。
3. 通常の圏 C に対し、相対関手単体集合から strict transport を構成する。
   Kan 値 weighted nerve と scaffold の比較を先に完成させ、元の left fibration を
   底 `nerve C` 上の同値まで復元する。scaffold の補助的な bar 型単体集合は
   明示的に構成するが、𝒮 の ∞ 余極限の存在・普遍性は主張しない。
4. strict diagram の比較を一般の `nerve C → SpaceInfinity` の coherent diagram と
   接続する。strict diagram の場合だけを分類した段階を F1d の完成とはしない。
   coherent representation の境界付き延長、選択空間の可縮性、パラメーター付きの
   比較をホーン充填で証明する。
5. left fibrations の相対関手の写像空間を構成し、unstraightening による写像空間の
   同値と本質的全射性を示す。ここで初めて straightening/unstraightening の
   関手 ∞ 圏の同値、単位・余単位、底変換との整合性を確立する。
6. この left fibration・𝒮 値の場合を完了した後で、cocartesian 射を保つ相対関手と
   Cat_∞ の対象付き構成へ拡張する。Cat_∞ の単なる coslice は left fibration しか
   与えないので、一般の cocartesian 分類の代用にはしない。

宇宙 u の Kan 複体・quasicategory を対象にした coherent nerve は宇宙 u+1 に置く。
小さい底を使う際には宇宙持ち上げを明示する。essentially small の一般形では小さい
代表への同値とその選択独立性も証明する。モデル構造や未証明の分類定理は使わず、
𝒮・Cat_∞ の極限・余極限は F2 の担当範囲として保持する。
