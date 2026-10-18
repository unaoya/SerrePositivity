module

public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentSimplexData

public import SerrePositivity.InfinityCategories.DoldKanComparison.PathSplitComposition

public import SerrePositivity.InfinityCategories.DoldKanComparison.CubeAWComposition

public import SerrePositivity.InfinityCategories.DoldKanComparison.AWCubeSum

public import SerrePositivity.InfinityCategories.DoldKanComparison.AWCubeRestriction

public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentComposition
public import SerrePositivity.InfinityCategories.DoldKanComparison.DescendingDeletion

public import SerrePositivity.InfinityCategories.DoldKanComparison.CubeOneBoundary

public import SerrePositivity.InfinityCategories.DoldKanComparison.PathEvaluation
public import SerrePositivity.InfinityCategories.DoldKanComparison.CubeLowDimensional
public import SerrePositivity.InfinityCategories.DoldKanComparison.HomSpace
public import SerrePositivity.InfinityCategories.DoldKanComparison.SimplicialCategory
public import SerrePositivity.InfinityCategories.DoldKanComparison.AWPreservation
public import SerrePositivity.InfinityCategories.DoldKanComparison.AWPullback
public import SerrePositivity.InfinityCategories.DoldKanComparison.AWUnitMap
public import SerrePositivity.InfinityCategories.DoldKanComparison.DoldKanIso
public import SerrePositivity.InfinityCategories.DoldKanComparison.ConnectiveHom
public import SerrePositivity.InfinityCategories.DoldKanComparison.StandardModule
public import SerrePositivity.InfinityCategories.DoldKanComparison.Sign
public import SerrePositivity.InfinityCategories.DoldKanComparison.Vertices

/-!
# Dold–Kan 豊穣化と dg nerve の比較の入口

概要：DK Hom と AW 合成の単体的圏とその coherent nerve を公開する。
方針：標準成分模型を実際の Mathlib Γ と同定し、N4 の線形充填で局所 Kan 性を得る。
規約：coherent nerve から dg nerve への比較写像と ∞ 圏の同値は残る。
使われ方：HA 1.3.1.13・1.3.1.17、Kerodon 2.5.7–2.5.9 の γ1.5 の入口。
-/
