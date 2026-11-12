module
public import SerrePositivity.KST.SConstruction.StableSuspensionAssemblyAction
public import SerrePositivity.KST.SConstruction.StableOneDirectionPointedFunctor
public import SerrePositivity.KST.SConstruction.StableBoundaryPointedFunctor
public import SerrePositivity.KST.SConstruction.PointedSSetSuspensionFunctor
public import SerrePositivity.KST.SConstruction.PointedSSetWhisker
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialTransformation

/-!
概要：元の suspension 組み立てを同じ全族の厳密点つき変換に束ねる。
方針：保存済みの全基点固定族自然性を標準豊穣の前後合成で読む。
規約：段比較のみを構成する。使われ方：有限 native BF 再帰の右脚。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet InfinityCategories LocalizingInvariants

/-- 概要：同じ一次方向商の元の suspension を保つ段関手。
方針：元の標準点つき suspension を後合成する。
規約：元の円を保持。使われ方：同じ実組み立ての始域。 -/
def stableSuspensionAssemblySourceFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} PointedSSetObject.{u} :=
  (stableOneDirectionPointedEnrichedFunctor r).comp SSet pointedSSetSuspensionEnrichedFunctor

/-- 概要：同じ元の suspension 組み立て射。
方針：元の射を標準点つき値間の射として保持する。
規約：射の変更なし。使われ方：全族変換の成分。 -/
def stableSuspensionAssemblyMap (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableSuspensionAssemblySourceFunctor r).obj C ⟶
      (stableBoundaryPointedEnrichedFunctor (r + 1)).obj C :=
  oneDirectionSuspensionAssembly r (stableCategoryModel C)

/-- 概要：同じ組み立ては全 Hom の前後合成と可換する。
方針：元の全族自然性を標準点つき豊穣の式へ移す。
規約：元の全高次入力を保持。使われ方：厳密自然変換の包装。 -/
lemma stableSuspensionAssembly_whisker (r : ℕ) (C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableSuspensionAssemblySourceFunctor r).map C D ≫
        eHomWhiskerLeft SSet ((stableSuspensionAssemblySourceFunctor r).obj C)
          (stableSuspensionAssemblyMap r D) =
      (stableBoundaryPointedEnrichedFunctor (r + 1)).map C D ≫
        eHomWhiskerRight SSet (stableSuspensionAssemblyMap r C)
          ((stableBoundaryPointedEnrichedFunctor (r + 1)).obj D) := by
  rw [pointedSSetObject_whiskerLeft, pointedSSetObject_whiskerRight]
  exact (Category.assoc _ _ _).trans (stableSuspensionAssembly_action r C D)

/-- 概要：同じ元の組み立てを全自然同値族に自然な変換にする。
方針：検証済みの全 Hom 可換式を束ねる。
規約：元の成分を保持。使われ方：同じ Ex∞ 後の隣接段 span。
-/
def stableSuspensionAssemblyTransformation (r : ℕ) :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (stableSuspensionAssemblySourceFunctor r) (stableBoundaryPointedEnrichedFunctor (r + 1)) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialTransformationOfWhisker _ _ (stableSuspensionAssemblyMap r)
    (stableSuspensionAssembly_whisker r)

/-- 概要：変換の成分は同じ元の実組み立て。
方針：標準豊穣包装の成分を展開する。
規約：元の射を固定。使われ方：元の Ω 条件との照合。 -/
lemma stableSuspensionAssemblyTransformation_app (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableSuspensionAssemblyTransformation r).app C =
      eHomEquiv SSet (stableSuspensionAssemblyMap r C) := rfl

end SerrePositivity.KST.SConstruction
