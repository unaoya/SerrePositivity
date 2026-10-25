module
public import SerrePositivity.KST.SConstruction.Cofinality.CompleteSource
public import SerrePositivity.KST.SConstruction.Cofinality.FullyFaithful
public import SerrePositivity.KST.SConstruction.Cofinality.ZeroComparison

/-!
概要：K-cof 所有の共終性補助結果を集約する。
方針：新規葉だけを公開し、既存の S• 集約には逆依存を加えない。
規約：一般の Thomason 共終性は未完成。完備始域の特殊場合と区別する。
使われ方：K-cof の限定ビルドと公理監査の入口。
-/
