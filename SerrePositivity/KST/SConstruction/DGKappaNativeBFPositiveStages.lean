module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFStepValue

/-!
概要：同じ未完備 native 一四角形の全正 BF 段を、前向き弱比較とともに実構成する。
方針：実際の前段へ延長した左脚の弱同値性を保ち、同じ実次段構成を再帰する。
規約：未証明の Ω 条件を帰納入力にしない。使われ方：同じ四辺の全段同時構成。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories NonConnective
open Spectra SimplicialModel
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (r : ℕ)
  (S : DGKappaNativeBFFiniteStage.{u, v} R D I r)

/-- 概要：同じ実際の前段への延長左脚は局所化で可逆。
方針：元の S₁ 左脚と前段比較の suspension の可逆性を合成する。
規約：前段の実値を使う。使われ方：次段の前向き比較の弱同値性。 -/
lemma dgKappaNativeBFFiniteStepLeftMap_localized_isIso
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r).obj C).obj ⟶
        ((dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S).obj C).obj from
          dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r S.functor S.comparison C).right) := by
  letI : KanComplex (S.functor.obj C).obj.right := S.kan C
  letI : KanComplex
      (((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C).obj).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity_kanComplex _
  let c : ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I r).obj C).obj ⟶
      (S.functor.obj C).obj := S.comparison C
  have hp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism c.right := kanPiIsomorphism_of_localized_isIso _ (S.weak C)
  have hσ : IsIso (AnodyneHomotopy.anodyneQ.map
      (PointedSimplicialSet.circle.{max (u + 1) v} ◁ c).right) :=
    suspensionImage_isIso_of_piIsomorphism AnodyneHomotopy.anodyneQ
      (Localization.inverts _ anodyneExtensions) c hp
  have hleft : IsIso (AnodyneHomotopy.anodyneQ.map (stableKanAssemblyLeftMap r C.obj).right) :=
    stableKanAssemblyLeftMap_localized_isIso r C.obj
  change IsIso (AnodyneHomotopy.anodyneQ.map
    ((stableKanAssemblyLeftMap r C.obj).right ≫
      (PointedSimplicialSet.circle.{max (u + 1) v} ◁ c).right))
  have h := AnodyneHomotopy.anodyneQ.map_comp (stableKanAssemblyLeftMap r C.obj).right
    (PointedSimplicialSet.circle.{max (u + 1) v} ◁ c).right
  exact h.symm ▸ IsIso.comp_isIso' hleft hσ

/-- 概要：同じ元の隣接正段への次段比較は局所化で可逆。
方針：同じ実円柱押し出しの一般定理へ元の延長左脚の可逆性を渡す。
規約：比較の存在を追加入力しない。使われ方：有限 BF 再帰の次の弱比較。 -/
lemma dgKappaNativeBFFiniteStepComparison_localized_isIso
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (show ((dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1)).obj C).obj ⟶
        ((dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S).obj C).obj from
          dgKappaNativeBFFiniteStepComparison.{u, v} R D I r S C).right) :=
  pointedEnrichedCylinderCompletionRight_localized_isIso
    (dgKappaNativeBFFiniteAssemblySourceFunctor.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeftTargetFunctor.{u, v} R D I r S)
    (dgKappaNativeBFFiniteBoundaryFunctor.{u, v} R D I (r + 1))
    (dgKappaNativeBFFiniteStepLeftMap.{u, v} R D I r S.functor S.comparison)
    (dgKappaNativeBFFiniteAssemblyRightMap.{u, v} R D I r)
    (dgKappaNativeBFFiniteStepLeft_whisker.{u, v} R D I r
      S.functor S.comparison S.naturality)
    (dgKappaNativeBFFiniteAssemblyRight_whisker.{u, v} R D I r) C
    (dgKappaNativeBFFiniteStepLeftMap_localized_isIso.{u, v} R D I r S C)

/-- 概要：同じ実次段構成は全ての帰納条件を保つ。
方針：構成済みの元の比較・全自然性・Kan 性・弱比較を束ねる。
規約：有限入力に限定。使われ方：全正段の実再帰。 -/
def dgKappaNativeBFFiniteNextStage : DGKappaNativeBFFiniteStage.{u, v} R D I (r + 1) where
  functor := dgKappaNativeBFFiniteStepFunctor.{u, v} R D I r S
  comparison := dgKappaNativeBFFiniteStepComparison.{u, v} R D I r S
  naturality := dgKappaNativeBFFiniteStepComparison_whisker.{u, v} R D I r S
  kan := dgKappaNativeBFFiniteStep_kanComplex.{u, v} R D I r S
  weak := dgKappaNativeBFFiniteStepComparison_localized_isIso.{u, v} R D I r S

/-- 概要：同じ元の零段評価を基底とする、全正 BF 段の実構成。
方針：同じ実次段構成を実際の前段に再帰適用する。
規約：Ω 条件を仮定しない。使われ方：同じ有限四角形のスペクトル化。 -/
def dgKappaNativeBFFinitePositiveStage : (n : ℕ) → DGKappaNativeBFFiniteStage.{u, v} R D I n
  | 0 => dgKappaNativeBFFiniteInitialStage.{u, v} R D I
  | n + 1 => dgKappaNativeBFFiniteNextStage.{u, v} R D I n
      (dgKappaNativeBFFinitePositiveStage n)

end SerrePositivity.KST.SConstruction
