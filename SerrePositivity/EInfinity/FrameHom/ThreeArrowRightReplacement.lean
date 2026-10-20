module

public import SerrePositivity.EInfinity.FrameHom.WeakThreeArrow
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

namespace SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement
open SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  {X Y : C}

abbrev arrow (S : LeftTrivialThreeArrow X Y) : Arrow C := Arrow.mk S.rightMap

def arrowMap {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) : arrow S ⟶ arrow T :=
  Arrow.homMk (𝟙 Y) f.right (by
    change 𝟙 Y ≫ T.rightMap = S.rightMap ≫ f.right
    rw [Category.id_comp]
    exact f.right_w.symm)

lemma arrowMap_id (S : LeftTrivialThreeArrow X Y) : arrowMap (𝟙 S) = 𝟙 (arrow S) := rfl

lemma arrowMap_comp {S T U : LeftTrivialThreeArrow X Y} (f : S ⟶ T) (g : T ⟶ U) :
    arrowMap (f ≫ g) = arrowMap f ≫ arrowMap g := by
  apply Arrow.hom_ext
  · exact (Category.id_comp _).symm
  · rfl

abbrev intermediate (S : LeftTrivialThreeArrow X Y) : C := fib.Z.obj (arrow S)
abbrev first (S : LeftTrivialThreeArrow X Y) : Y ⟶ intermediate fib S := fib.i.app (arrow S)
abbrev last (S : LeftTrivialThreeArrow X Y) : intermediate fib S ⟶ S.right :=
  fib.p.app (arrow S)
abbrev intermediateMap {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) := fib.Z.map (arrowMap f)

lemma fac (S : LeftTrivialThreeArrow X Y) : first fib S ≫ last fib S = S.rightMap :=
  congr_app fib.fac (arrow S)

lemma map_first {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) :
    first fib S ≫ intermediateMap fib f = first fib T := by
  have h := fib.i.naturality (arrowMap f)
  exact h.symm.trans (Category.id_comp _)

lemma map_last {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) :
    intermediateMap fib f ≫ last fib T = last fib S ≫ f.right :=
  fib.p.naturality (arrowMap f)

lemma last_trivialFibration (S : LeftTrivialThreeArrow X Y) :
    trivialFibrations C (last fib S) := by
  refine ⟨fib.hp _, ?_⟩
  apply (weakEquivalences C).of_precomp (first fib S) _ (fib.hi _).2
  exact (fac fib S).symm ▸ S.right_mem

abbrev left (S : LeftTrivialThreeArrow X Y) : C := pullback S.middle (last fib S)
abbrev fst (S : LeftTrivialThreeArrow X Y) : left fib S ⟶ S.left := pullback.fst _ _
abbrev snd (S : LeftTrivialThreeArrow X Y) : left fib S ⟶ intermediate fib S := pullback.snd _ _

lemma fst_trivialFibration (S : LeftTrivialThreeArrow X Y) :
    trivialFibrations C (fst fib S) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback S.middle (last fib S)).flip
    (last_trivialFibration fib S)

def leftMap {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) : left fib S ⟶ left fib T :=
  pullback.map S.middle (last fib S) T.middle (last fib T)
    f.left (intermediateMap fib f) f.right f.middle_w (map_last fib f).symm

lemma leftMap_fst {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) :
    leftMap fib f ≫ fst fib T = fst fib S ≫ f.left := pullback.lift_fst _ _ _

lemma leftMap_snd {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) :
    leftMap fib f ≫ snd fib T = snd fib S ≫ intermediateMap fib f := pullback.lift_snd _ _ _

lemma leftMap_id (S : LeftTrivialThreeArrow X Y) : leftMap fib (𝟙 S) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [leftMap_fst]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [leftMap_snd]
    change snd fib S ≫ fib.Z.map (arrowMap (𝟙 S)) = 𝟙 _ ≫ snd fib S
    rw [arrowMap_id, fib.Z.map_id, Category.comp_id, Category.id_comp]

lemma leftMap_comp {S T U : LeftTrivialThreeArrow X Y} (f : S ⟶ T) (g : T ⟶ U) :
    leftMap fib (f ≫ g) = leftMap fib f ≫ leftMap fib g := by
  apply pullback.hom_ext
  · rw [leftMap_fst, Category.assoc, leftMap_fst, ← Category.assoc, leftMap_fst]
    exact (Category.assoc _ _ _).symm
  · rw [leftMap_snd, Category.assoc, leftMap_snd, ← Category.assoc, leftMap_snd]
    change _ ≫ fib.Z.map (arrowMap (f ≫ g)) = (_ ≫ fib.Z.map (arrowMap f)) ≫
      fib.Z.map (arrowMap g)
    rw [arrowMap_comp, fib.Z.map_comp, Category.assoc]

/-- 同じ関手的分解と元の中間射の pullback による特殊な三本矢。 -/
def obj (S : LeftTrivialThreeArrow X Y) : SpecialHammock X Y where
  left := left fib S
  right := intermediate fib S
  leftMap := fst fib S ≫ S.leftMap
  middle := snd fib S
  rightMap := first fib S
  left_mem := (trivialFibrations C).comp_mem _ _ (fst_trivialFibration fib S) S.left_mem
  right_mem := fib.hi _

def map {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) : obj fib S ⟶ obj fib T where
  left := leftMap fib f
  right := intermediateMap fib f
  left_w := by
    change leftMap fib f ≫ (fst fib T ≫ T.leftMap) = fst fib S ≫ S.leftMap
    rw [← Category.assoc, leftMap_fst, Category.assoc, f.left_w]
  middle_w := (leftMap_snd fib f).symm
  right_w := map_first fib f

/-- 元の全対象・全射の右脚を関手的に置き換える。 -/
def functor : LeftTrivialThreeArrow X Y ⥤ SpecialHammock X Y where
  obj := obj fib
  map := map fib
  map_id S := by
    apply ArrowSpan.hom_ext
    · exact leftMap_id fib S
    · change fib.Z.map (arrowMap (𝟙 S)) = 𝟙 _
      rw [arrowMap_id, fib.Z.map_id]
  map_comp f g := by
    apply ArrowSpan.hom_ext
    · exact leftMap_comp fib f g
    · change fib.Z.map (arrowMap (f ≫ g)) = fib.Z.map (arrowMap f) ≫ fib.Z.map (arrowMap g)
      rw [arrowMap_comp, fib.Z.map_comp]

/-- 元の pullback の射影と自明 fibration による、元の三本矢への自然変換。 -/
def counit : functor fib ⋙ specialInclusion ⟶ 𝟭 (LeftTrivialThreeArrow X Y) where
  app S :=
    { left := fst fib S
      right := last fib S
      left_w := rfl
      middle_w := pullback.condition.symm
      right_w := fac fib S }
  naturality _ _ f := ArrowSpan.hom_ext _ _ (leftMap_fst fib f) (map_last fib f)

include fib in
/-- 同じ元の特殊な三本矢の包含の nerve は、関手的置換の余単位から反転。 -/
lemma inclusion_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (specialInclusion : SpecialHammock X Y ⥤ LeftTrivialThreeArrow X Y))) :=
  FullyFaithfulNerveRetraction.of_counit specialInclusion (functor fib) (counit fib)

end SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacement
