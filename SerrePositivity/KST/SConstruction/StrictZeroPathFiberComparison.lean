module
public import SerrePositivity.KST.SConstruction.IteratedPathHomotopyFiber
public import SerrePositivity.KST.Comparison.AlternativeFiberCriterion
public import SerrePositivity.KST.Spectra.PathContractibility

/-! # 厳密な零合成から既存の path homotopy fiber への比較
概要：元の全空間への零合成を、定数 path と共に既存の点つき pullback の底へ持ち上げる。
方針：path の基点包含は実収縮で局所化同型であり、homotopy pullback の別分解判定を適用する。
規約：源はまだ点つき・Kan と仮定しない。使われ方：元の反復経路零行の fiber 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.SimplicialModel SerrePositivity.KST.Comparison
open Spectra
open scoped Simplicial

/-- 基点始点の path 空間の基点包含は元の実収縮により局所化同型。 -/
lemma basedPathBasepoint_localized_isIso (B : PointedSimplicialSet.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (basedPathSpace B).hom) := by
  let Q := AnodyneHomotopy.anodyneQ
  let P := basedPathSpace B
  let H : SSet.Homotopy (toUnit P.right ≫ P.hom) (𝟙 P.right) := {
    h := pathContraction B
    h₀ := pathContraction_zero B
    h₁ := pathContraction_one B
    rel := by
      apply NatTrans.ext
      funext d
      apply ConcreteCategory.hom_ext
      intro x
      exact False.elim x.1.property }
  have hi : P.hom ≫ toUnit P.right = 𝟙 _ := isTerminalTensorUnit.hom_ext _ _
  exact ⟨⟨Q.map (toUnit P.right),
    (Q.map_comp _ _).symm.trans ((congrArg Q.map hi).trans (Q.map_id _)),
    (Q.map_comp _ _).symm.trans
      ((AnodyneHomotopy.map_homotopy_eq Q (Localization.inverts Q anodyneExtensions) H).trans
        (Q.map_id _))⟩⟩

/-- 厳密な零合成から定数 path を用いて既存の homotopy fiber の底への射を作る。 -/
def strictZeroPathFiberMap {A : SSet.{u}} {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (a : A ⟶ E.right) (ha : a ≫ f.right = toUnit A ≫ B.hom) :
    A ⟶ (pathHomotopyFiber f).right :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (pathEndpoint B) f).lift
    (toUnit A ≫ (basedPathSpace B).hom) a (by
      rw [Category.assoc, Under.w (pathEndpoint B)]
      exact ha.symm)

/-- 元の homotopy fiber への比較の path 成分は定数 path。 -/
lemma strictZeroPathFiberMap_path {A : SSet.{u}} {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (a : A ⟶ E.right) (ha : a ≫ f.right = toUnit A ≫ B.hom) :
    strictZeroPathFiberMap f a ha ≫ (pullback.fst (pathEndpoint B) f).right =
      toUnit A ≫ (basedPathSpace B).hom :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (pathEndpoint B) f).lift_fst _ _ _

/-- 元の homotopy fiber への比較の全空間への射影は元の射。 -/
lemma strictZeroPathFiberMap_projection {A : SSet.{u}} {E B : PointedSimplicialSet.{u}}
    (f : E ⟶ B) (a : A ⟶ E.right) (ha : a ≫ f.right = toUnit A ≫ B.hom) :
    strictZeroPathFiberMap f a ha ≫ (pathHomotopyFiberProjection f).right = a :=
  (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (pathEndpoint B) f).lift_snd _ _ _

/-- 零合成の元の四角形が homotopy pullback なら既存の path homotopy fiber への比較は局所化同型。 -/
lemma strictZeroPathFiberMap_localized_isIso_of_homotopyPullback
    {A : SSet.{u}} {E B : PointedSimplicialSet.{u}} [KanComplex B.right]
    (f : E ⟶ B) (a : A ⟶ E.right) (ha : a ≫ f.right = toUnit A ≫ B.hom)
    (h : IsHomotopyPullback (CommSq.mk ha)) :
    IsIso (AnodyneHomotopy.anodyneQ.map (strictZeroPathFiberMap f a ha)) := by
  exact (isHomotopyPullback_iff_alternative_fiber (CommSq.mk ha).flip
    (basedPathSpace B).hom (basedPathBasepoint_localized_isIso B) (pathEndpoint B).right
    ((SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance) (Under.w (pathEndpoint B))
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (pathEndpoint B) f).flip (strictZeroPathFiberMap f a ha)
    (strictZeroPathFiberMap_projection f a ha) (strictZeroPathFiberMap_path f a ha)).mp
      ((isHomotopyPullback_flip_iff (CommSq.mk ha)).mpr h)

end SerrePositivity.KST.SConstruction
