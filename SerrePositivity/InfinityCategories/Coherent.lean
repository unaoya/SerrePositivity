module

public import SerrePositivity.InfinityCategories.Coherent.Path
public import SerrePositivity.InfinityCategories.Coherent.Quasicategory
public import SerrePositivity.InfinityCategories.Coherent.HornHollow
public import SerrePositivity.InfinityCategories.Coherent.CompositionCompatibility
public import SerrePositivity.InfinityCategories.Coherent.MixedCompatibility
public import SerrePositivity.InfinityCategories.Coherent.CompositionRecovery
public import SerrePositivity.InfinityCategories.Coherent.IntervalChoice
public import SerrePositivity.InfinityCategories.Coherent.IntervalRecovery
public import SerrePositivity.InfinityCategories.Coherent.IntervalFunctor
public import SerrePositivity.InfinityCategories.Coherent.HornFunctor
public import SerrePositivity.InfinityCategories.Coherent.CompositionFace
public import SerrePositivity.InfinityCategories.Coherent.PathHollow
public import SerrePositivity.InfinityCategories.Coherent.PathNerve
public import SerrePositivity.InfinityCategories.Coherent.ZeroFaceCompatibility
public import SerrePositivity.InfinityCategories.Coherent.FaceRestriction
public import SerrePositivity.InfinityCategories.Coherent.FaceHom
public import SerrePositivity.InfinityCategories.Coherent.HornCells
public import SerrePositivity.InfinityCategories.Coherent.HornData
public import SerrePositivity.InfinityCategories.Coherent.HollowCube
public import SerrePositivity.InfinityCategories.Coherent.HollowCylinder

/-!
# Coherent nerve の quasicategory 性

概要：局所 Kan な単体的圏の Mathlib の SimplicialNerve は quasicategory である。
方針：Path[n] の空洞部分への貼合せ、Kan 延長、豊穣関手の復元により内部ホーンを充填する。
規約：前提は単体的圏と各 Hom の Kan 性のみ。γ1 の最終 instance を公開する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.1 の証明の入口。
-/
