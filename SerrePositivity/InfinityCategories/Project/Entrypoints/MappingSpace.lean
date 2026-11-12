module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Edges
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.PinchedUniversal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceTrivialFibration

/-!
概要：pinched 写像空間の定義・Kan 性・π₀・関手性を読むための入口。
方針：既存の公開モジュールを public import し、主要宣言の所在を示す。
規約：右 pinched 模型を共通の写像空間として保ち、定義・証明は移さない。
使われ方：写像空間の基礎の目次。Core 集約からも利用できる。

## 定義と読み順

* `PinchedHom/Basic`・`Edges`：`pinchedHom`、頂点と辺の対応。
* `MappingSpaceMap`：`pinchedHomMap` による関手性。
* `MappingSpacePiZero`：`pinchedHomPiZeroEquiv` とホモトピー圏の Hom。
* `MappingSpaceRightKan`：右写像空間の Kan 性。
* `MappingSpaceLeft`：反対圏による左 pinched 模型。
* `PinchedSlice`：slice の頂点 fiber との同型。
* `PinchedUniversal`：join を使う curry・uncurry の普遍性。
* `MappingSpaceFibration`・`MappingSpaceTrivialFibration`：写像空間への
  作用の右 fibration 性・trivial Kan fibration 性。

左右の模型と区間模型との比較は、引き続き
`F1/MappingSpaceModelEquivalence` を参照する。
-/
