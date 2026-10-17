module

public import SerrePositivity.InfinityCategories.Coherent.Path
public import SerrePositivity.InfinityCategories.Coherent.HollowCylinder

/-!
# Coherent nerve の基盤

概要：局所 Kan な単体的圏の coherent nerve の証明に使う基盤を集約する。
方針：Path[n] の包含規約と空洞立方体の延長を個別に証明する。
規約：現段階では γ1 全体の quasicategory instance は未実装。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.1 の証明の入口。
-/
