module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.Cardinals
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.SmallPieceChains

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.PartialColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.PresentationAssembly

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.OrdinalInterleaving

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FullCosliceRestriction
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.IndCompactEmbedding

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FactorizationEdgeLift
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FullCompactFactorization

/-!
概要：accessible 引き戻し一般版の所有する新規界面を集約する。
方針：共通 κ₀ と μ、小表示部分、長さ κ₀ の相対交互構成、生成表示を順に接続する。
規約：既存 P の葉を読み取り専用で使い、fiber 版の全小余極限保存を一般版へ追加しない。
使われ方：P-d の専用ビルド・公理監査と P-e8 への公開名の引き継ぎ。
-/
