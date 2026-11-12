module
public import SerrePositivity.KST.SConstruction.StableOneDirectionCoreComparison
public import SerrePositivity.KST.SConstruction.CoordinateEnrichedAssembly
public import SerrePositivity.KST.SConstruction.StableMultiRealizationAction

/-!
概要：元の一次方向実現と S₁ 比較を、全自然同値パラメータに保つ。
方針：既存の対角作用を同じ固定次数へ制限し、全 core 比較を次数ごとに評価する。
規約：実現段階の比較に限定する。BF 関手の一般構成は行わない。
使われ方：有限 native 四角形の隣接正段比較を元の二胞体に自然にする。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories LocalizingInvariants

/-- 概要：同じ一次方向実現へ全自然同値族を作用させる。
方針：元の全図式作用と元の対角豊穣関手を合成する。
規約：元の実現値を保持する。使われ方：商への作用の降下。 -/
def stableOneDirectionEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} SSetInternalObject.{u} :=
  (stableOneDirectionObjectEnrichedFunctor r).comp SSet
    simplicialSSetDiagramDiagonalEnrichedFunctor

/-- 概要：実現の値は元の一次方向図式の対角。
方針：二つの図式制限を展開する。
規約：同じ安定値を固定する。使われ方：元の S₁ 比較との型照合。 -/
lemma stableOneDirectionEnrichedFunctor_obj (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((stableOneDirectionEnrichedFunctor r).obj C).obj =
      (oneDirectionRealizationFunctor r).obj (stableCategoryModel C) := rfl

/-- 概要：元の一次方向実現の全パラメータ作用。
方針：元の全多次数作用を同じ対角に制限する。
規約：全単体を保持する。使われ方：全零境界の保存。 -/
def stableOneDirectionAction (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    ((oneDirectionRealizationFunctor r).obj (stableCategoryModel C)) ⊗
      (C ⟶[SSet.{u}] D) ⟶
        (oneDirectionRealizationFunctor r).obj (stableCategoryModel D) :=
  coordinateEnrichedDiagonalAction (stableMultiSCoreEnrichedDiagram (r + 1))
    (multiIndexDiagonal r ⋙ oneDirectionIndex r) C D

/-- 概要：豊穣射の評価は同じ元の全実現作用。
方針：同じ対角作用の定義を展開する。
規約：全パラメータの等式。使われ方：元の作用法則の回収。 -/
lemma stableOneDirectionEnrichedFunctor_action (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    uncurry ((stableOneDirectionEnrichedFunctor r).map C D) =
      stableOneDirectionAction r C D := rfl

/-- 概要：全作用の各単体は同じ多次数の全 core 作用。
方針：既存の対角作用の評価式を使う。
規約：高次入力 p を固定する。使われ方：境界保存と比較自然性の検証。 -/
lemma stableOneDirectionAction_app (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u})
    (n : SimplexCategoryᵒᵖ)
    (x : ((oneDirectionRealizationFunctor r).obj (stableCategoryModel C)).obj n)
    (p : (C ⟶[SSet.{u}] D).obj n) :
    (stableOneDirectionAction r C D).app n (x, p) =
      (uncurry (((stableMultiSCoreEnrichedDiagram (r + 1)).obj
        ((oneDirectionIndex r).obj (fun _ => n))).map C D)).app n (x, p) :=
  coordinateEnrichedDiagonalAction_app (stableMultiSCoreEnrichedDiagram (r + 1))
    (multiIndexDiagonal r ⋙ oneDirectionIndex r) C D n x p

/-- 概要：元の S₁ 実現比較は全自然同値パラメータと厳密に可換する。
方針：元の core 比較の全族自然性を対角の同じ単体に適用する。
規約：対象ごとの可換性で代用しない。使われ方：有限四角形の全 Ω 比較。 -/
lemma stableOneDirectionComparison_action (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (oneDirectionRealizationComparison r (stableCategoryModel C) ▷
        (C ⟶[SSet.{u}] D)) ≫ stableMultiRealizationAction r C D =
      stableOneDirectionAction r C D ≫
        oneDirectionRealizationComparison r (stableCategoryModel D) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro z
  have hn := congrArg (fun q => q.app n z)
    ((stableMultiSOneCoreComparison r (fun _ => n)).property C D)
  have ht := stableMultiRealizationAction_app r C D n
    ((oneDirectionRealizationComparison r (stableCategoryModel C)).app n z.1) z.2
  have hs := stableOneDirectionAction_app r C D n z.1 z.2
  exact ht.trans (hn.trans
    (congrArg (fun x => (oneDirectionRealizationComparison r
      (stableCategoryModel D)).app n x) hs.symm))

end SerrePositivity.KST.SConstruction
