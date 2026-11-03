module
public import SerrePositivity.DifferentialGraded.Bimodule.DiagonalRestriction
public import SerrePositivity.DifferentialGraded.Derived.AssociatorLeft
public import SerrePositivity.DifferentialGraded.Derived.AssociatorMiddle

public import SerrePositivity.DifferentialGraded.Derived.Paired
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddle.FunctorCoherence
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensor


public import SerrePositivity.DifferentialGraded.Derived.LeftUnit
public import SerrePositivity.DifferentialGraded.Derived.Basic

public import SerrePositivity.DifferentialGraded.Resolution.Composition
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Path
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Append.BoundaryCompatibility
public import SerrePositivity.DifferentialGraded.Resolution.FixedObject


public import SerrePositivity.DifferentialGraded.Tensor.ResolvedRestriction
public import SerrePositivity.DifferentialGraded.Tensor.Graded


/-! # U12e-generalの再利用可能な成果の独立入口

## 概要
棚卸し(A)の一般APIをまとめ、K-flat dg圏分解の存在・比較と個々の制限squareを公開する。

## 方針
既存パスを保持し、(A)のproductionモジュールを依存で覆う入口だけをimportする。

## 規約と注意
U12e-generalは部分実装済み・中断・未受入。R1〜R7の完全coherenceを主張しない。
局所版Derived.BimoduleLocalはこの入口に依存しない。検査モジュールはここからimportしない。

## 使われ方
Hom非平坦dg圏のMorita・tensor・Hochschild型構成・K理論や、M9で平坦性が崩れた場合の再開に使う。
公開名と仮定の参照先はformalization-plans/dg-theory-u12e-general-inventory.md。
-/
