module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow
public import SerrePositivity.EInfinity.FrameHom.FullyFaithfulNerveRetraction
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# 元の三本矢の右脚の関手的な置換

概要：左脚が自明な三本矢の右脚も自明 cofibration に置き換え、包含を反転する。
方針：元の右脚を関手的に分解し、中間射をその自明 fibration に沿って pullback。
規約：始域の cofibrancy や単体集合モデルは不要。元の左脚の自明性を保持する。
使われ方：Low 命題3.5 の三本矢の比較の右脚の工程。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement
open _root_.SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  {X Y : C}

abbrev arrow (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) : Arrow C := Arrow.mk S.rightMap

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.arrow export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (arrow)


def arrowMap {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y} (f : S ⟶ T) : arrow S ⟶ arrow T :=
  Arrow.homMk (𝟙 Y) f.right (by
    change 𝟙 Y ≫ T.rightMap = S.rightMap ≫ f.right
    rw [Category.id_comp]
    exact f.right_w.symm)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.arrowMap export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (arrowMap)


lemma arrowMap_id (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) : arrowMap (𝟙 S) = 𝟙 (arrow S) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.arrowMap_id export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (arrowMap_id)


lemma arrowMap_comp {S T U : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y} (f : S ⟶ T) (g : T ⟶ U) :
    arrowMap (f ≫ g) = arrowMap f ≫ arrowMap g := by
  apply Arrow.hom_ext
  · exact (Category.id_comp _).symm
  · rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.arrowMap_comp export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (arrowMap_comp)


abbrev intermediate (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) : C := fib.Z.obj (arrow S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.intermediate export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (intermediate)

abbrev first (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) : Y ⟶ intermediate fib S := fib.i.app (arrow S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.first export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (first)

abbrev last (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) : intermediate fib S ⟶ S.right :=
  fib.p.app (arrow S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.last export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (last)

abbrev intermediateMap {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y} (f : S ⟶ T) := fib.Z.map (arrowMap f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.intermediateMap export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (intermediateMap)


lemma fac (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) : first fib S ≫ last fib S = S.rightMap :=
  congr_app fib.fac (arrow S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.fac export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (fac)


lemma map_first {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y} (f : S ⟶ T) :
    first fib S ≫ intermediateMap fib f = first fib T := by
  have h := fib.i.naturality (arrowMap f)
  exact h.symm.trans (Category.id_comp _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.map_first export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (map_first)


lemma map_last {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y} (f : S ⟶ T) :
    intermediateMap fib f ≫ last fib T = last fib S ≫ f.right :=
  fib.p.naturality (arrowMap f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.map_last export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (map_last)


lemma last_trivialFibration (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) :
    trivialFibrations C (last fib S) := by
  refine ⟨fib.hp _, ?_⟩
  apply (weakEquivalences C).of_precomp (first fib S) _ (fib.hi _).2
  exact (fac fib S).symm ▸ S.right_mem

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.last_trivialFibration export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (last_trivialFibration)


abbrev left (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) : C := pullback S.middle (last fib S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.left export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (left)

abbrev fst (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) : left fib S ⟶ S.left := pullback.fst _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.fst export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (fst)

abbrev snd (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) : left fib S ⟶ intermediate fib S := pullback.snd _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.snd export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (snd)


lemma fst_trivialFibration (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) :
    trivialFibrations C (fst fib S) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback S.middle (last fib S)).flip
    (last_trivialFibration fib S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.fst_trivialFibration export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (fst_trivialFibration)


def leftMap {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y} (f : S ⟶ T) : left fib S ⟶ left fib T :=
  pullback.map S.middle (last fib S) T.middle (last fib T)
    f.left (intermediateMap fib f) f.right f.middle_w (map_last fib f).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.leftMap export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (leftMap)


lemma leftMap_fst {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y} (f : S ⟶ T) :
    leftMap fib f ≫ fst fib T = fst fib S ≫ f.left := pullback.lift_fst _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.leftMap_fst export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (leftMap_fst)


lemma leftMap_snd {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y} (f : S ⟶ T) :
    leftMap fib f ≫ snd fib T = snd fib S ≫ intermediateMap fib f := pullback.lift_snd _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.leftMap_snd export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (leftMap_snd)


lemma leftMap_id (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) : leftMap fib (𝟙 S) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [leftMap_fst]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [leftMap_snd]
    change snd fib S ≫ fib.Z.map (arrowMap (𝟙 S)) = 𝟙 _ ≫ snd fib S
    rw [arrowMap_id, fib.Z.map_id, Category.comp_id, Category.id_comp]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.leftMap_id export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (leftMap_id)


lemma leftMap_comp {S T U : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y} (f : S ⟶ T) (g : T ⟶ U) :
    leftMap fib (f ≫ g) = leftMap fib f ≫ leftMap fib g := by
  apply pullback.hom_ext
  · rw [leftMap_fst, Category.assoc, leftMap_fst, ← Category.assoc, leftMap_fst]
    exact (Category.assoc _ _ _).symm
  · rw [leftMap_snd, Category.assoc, leftMap_snd, ← Category.assoc, leftMap_snd]
    change _ ≫ fib.Z.map (arrowMap (f ≫ g)) = (_ ≫ fib.Z.map (arrowMap f)) ≫
      fib.Z.map (arrowMap g)
    rw [arrowMap_comp, fib.Z.map_comp, Category.assoc]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.leftMap_comp export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (leftMap_comp)


/-- 同じ関手的分解と元の中間射の pullback による特殊な三本矢。 -/
def obj (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y where
  left := left fib S
  right := intermediate fib S
  leftMap := fst fib S ≫ S.leftMap
  middle := snd fib S
  rightMap := first fib S
  left_mem := (trivialFibrations C).comp_mem _ _ (fst_trivialFibration fib S) S.left_mem
  right_mem := fib.hi _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.obj export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (obj)


def map {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y} (f : S ⟶ T) : obj fib S ⟶ obj fib T where
  left := leftMap fib f
  right := intermediateMap fib f
  left_w := by
    change leftMap fib f ≫ (fst fib T ≫ T.leftMap) = fst fib S ≫ S.leftMap
    rw [← Category.assoc, leftMap_fst, Category.assoc, f.left_w]
  middle_w := (leftMap_snd fib f).symm
  right_w := map_first fib f

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.map export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (map)


/-- 元の全対象・全射の右脚を関手的に置き換える。 -/
def functor : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y where
  obj := obj fib
  map := map fib
  map_id S := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext
    · exact leftMap_id fib S
    · change fib.Z.map (arrowMap (𝟙 S)) = 𝟙 _
      rw [arrowMap_id, fib.Z.map_id]
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext
    · exact leftMap_comp fib f g
    · change fib.Z.map (arrowMap (f ≫ g)) = fib.Z.map (arrowMap f) ≫ fib.Z.map (arrowMap g)
      rw [arrowMap_comp, fib.Z.map_comp]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.functor export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (functor)


/-- 元の pullback の射影と自明 fibration による、元の三本矢への自然変換。 -/
def counit : functor fib ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.specialInclusion ⟶ 𝟭 (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y) where
  app S :=
    { left := fst fib S
      right := last fib S
      left_w := rfl
      middle_w := pullback.condition.symm
      right_w := fac fib S }
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext _ _ (leftMap_fst fib f) (map_last fib f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.counit export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (counit)


include fib in
/-- 同じ元の特殊な三本矢の包含の nerve は、関手的置換の余単位から反転。 -/
lemma inclusion_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.specialInclusion : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.SpecialHammock X Y ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y))) :=
  _root_.SerrePositivity.EInfinity.FrameHom.FullyFaithfulNerveRetraction.of_counit _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.specialInclusion (functor fib) (counit fib)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.RightReplacement.inclusion_localized_isIso export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement (inclusion_localized_isIso)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowRightReplacement
