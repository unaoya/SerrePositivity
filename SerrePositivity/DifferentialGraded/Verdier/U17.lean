module
public import SerrePositivity.DifferentialGraded.Verdier.OrderSquare
public import SerrePositivity.DifferentialGraded.Verdier.SupportSquare
public import SerrePositivity.DifferentialGraded.Verdier.RetractSquare
public import SerrePositivity.DifferentialGraded.Verdier.ScalarDirectCompletion
public import SerrePositivity.DifferentialGraded.Verdier.MoritaPairEquivalence
public import SerrePositivity.DifferentialGraded.Verdier.DerivedKernelGraphSquare
public import SerrePositivity.DifferentialGraded.Verdier.GraphPairMorita
public import SerrePositivity.DifferentialGraded.Verdier.KernelComparisonNaturality

/-! # 局所 dg 商の U17 比較の公開入口

順序交換と論文の列比較、支持・retract、係数変更の直接 Verdier 局所化と完備化、
主導来 kernel 作用の指定商・perfect enhancement 正方形をまとめる。
各宣言に明記した局所 K-flat 条件、perfect 列条件、零部分圏の対応条件を保持する。
中心作用と群の作用はこの入口の範囲に含めない。
-/
