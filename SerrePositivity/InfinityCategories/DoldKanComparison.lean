module

public import SerrePositivity.InfinityCategories.DoldKanComparison.HomSpace
public import SerrePositivity.InfinityCategories.DoldKanComparison.NormalizedEquiv
public import SerrePositivity.InfinityCategories.DoldKanComparison.ConnectiveHom
public import SerrePositivity.InfinityCategories.DoldKanComparison.StandardModule
public import SerrePositivity.InfinityCategories.DoldKanComparison.Sign
public import SerrePositivity.InfinityCategories.DoldKanComparison.Vertices

/-!
# Dold–Kan 豊穣化と dg nerve の比較の入口

概要：標準の chain map 方程式の Hom 模型と N4 の写像空間との自然な比較を公開する。
方針：小さい単体的加群を構成し、宇宙の持ち上げを介して直接の線形充填を移す。
規約：豊穣合成、coherent nerve からの比較写像、∞ 圏の同値はまだ実装していない。
使われ方：HA 1.3.1.13・1.3.1.17、Kerodon 2.5.7–2.5.9 の γ1.5 の入口。
-/
