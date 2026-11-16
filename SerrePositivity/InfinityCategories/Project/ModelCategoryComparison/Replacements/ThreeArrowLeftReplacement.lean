module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.WeakThreeArrow
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FullyFaithfulNerveRetraction
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

/-!
# 元の三本矢の左脚の関手的な置換

概要：弱同値の三本矢の左脚を自明 fibration に置き換え、包含の nerve を反転する。
方針：元の左脚を関手的に分解し、中間射をその自明 cofibration に沿って pushout。
規約：始域の cofibrancy は不要。元のモデル圏と指定した関手的分解だけを使う。
使われ方：Low 命題3.5 の三本矢の比較の左脚の工程。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits _root_.HomotopicalAlgebra

namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement
open _root_.SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  {X Y : C}

abbrev arrow (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : Arrow C := Arrow.mk S.leftMap

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.arrow export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (arrow)


def arrowMap {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) : arrow S ⟶ arrow T :=
  Arrow.homMk f.left (𝟙 X) (by
    change f.left ≫ T.leftMap = S.leftMap ≫ 𝟙 X
    rw [Category.comp_id]
    exact f.left_w)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.arrowMap export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (arrowMap)


lemma arrowMap_id (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : arrowMap (𝟙 S) = 𝟙 (arrow S) := rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.arrowMap_id export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (arrowMap_id)


lemma arrowMap_comp {S T U : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) (g : T ⟶ U) :
    arrowMap (f ≫ g) = arrowMap f ≫ arrowMap g := by
  apply Arrow.hom_ext
  · rfl
  · exact (Category.id_comp _).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.arrowMap_comp export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (arrowMap_comp)


abbrev intermediate (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : C := cof.Z.obj (arrow S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.intermediate export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (intermediate)

abbrev first (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : S.left ⟶ intermediate cof S := cof.i.app (arrow S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.first export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (first)

abbrev last (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : intermediate cof S ⟶ X := cof.p.app (arrow S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.last export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (last)

abbrev intermediateMap {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) := cof.Z.map (arrowMap f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.intermediateMap export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (intermediateMap)


lemma fac (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : first cof S ≫ last cof S = S.leftMap :=
  congr_app cof.fac (arrow S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.fac export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (fac)


lemma map_first {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) :
    f.left ≫ first cof T = first cof S ≫ intermediateMap cof f :=
  cof.i.naturality (arrowMap f)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.map_first export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (map_first)


lemma map_last {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) :
    intermediateMap cof f ≫ last cof T = last cof S := by
  have h := cof.p.naturality (arrowMap f)
  exact h.trans (Category.comp_id _)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.map_last export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (map_last)


lemma first_trivialCofibration (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) :
    trivialCofibrations C (first cof S) := by
  refine ⟨cof.hi _, ?_⟩
  apply (weakEquivalences C).of_postcomp _ (last cof S) (cof.hp _).2
  exact (fac cof S).symm ▸ S.left_mem

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.first_trivialCofibration export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (first_trivialCofibration)


abbrev right (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : C := pushout (first cof S) S.middle

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.right export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (right)

abbrev inl (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : intermediate cof S ⟶ right cof S := pushout.inl _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.inl export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (inl)

abbrev inr (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : S.right ⟶ right cof S := pushout.inr _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.inr export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (inr)


lemma inr_trivialCofibration (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) :
    trivialCofibrations C (inr cof S) :=
  MorphismProperty.of_isPushout (IsPushout.of_hasPushout (first cof S) S.middle).flip
    (first_trivialCofibration cof S)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.inr_trivialCofibration export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (inr_trivialCofibration)


def rightMap {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) : right cof S ⟶ right cof T :=
  pushout.map (first cof S) S.middle (first cof T) T.middle
    (intermediateMap cof f) f.right f.left (map_first cof f).symm f.middle_w

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.rightMap export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (rightMap)


lemma inl_rightMap {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) :
    inl cof S ≫ rightMap cof f = intermediateMap cof f ≫ inl cof T :=
  pushout.inl_desc _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.inl_rightMap export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (inl_rightMap)


lemma inr_rightMap {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) :
    inr cof S ≫ rightMap cof f = f.right ≫ inr cof T := pushout.inr_desc _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.inr_rightMap export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (inr_rightMap)


lemma rightMap_id (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : rightMap cof (𝟙 S) = 𝟙 _ := by
  apply pushout.hom_ext
  · rw [inl_rightMap]
    change cof.Z.map (arrowMap (𝟙 S)) ≫ inl cof S = inl cof S ≫ 𝟙 _
    rw [arrowMap_id, cof.Z.map_id, Category.id_comp, Category.comp_id]
  · rw [inr_rightMap]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.rightMap_id export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (rightMap_id)


lemma rightMap_comp {S T U : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) (g : T ⟶ U) :
    rightMap cof (f ≫ g) = rightMap cof f ≫ rightMap cof g := by
  apply pushout.hom_ext
  · rw [inl_rightMap, ← Category.assoc, inl_rightMap, Category.assoc, inl_rightMap]
    change cof.Z.map (arrowMap (f ≫ g)) ≫ _ = cof.Z.map (arrowMap f) ≫ cof.Z.map (arrowMap g) ≫ _
    rw [arrowMap_comp, cof.Z.map_comp, Category.assoc]
  · rw [inr_rightMap, ← Category.assoc, inr_rightMap, Category.assoc, inr_rightMap]
    exact Category.assoc _ _ _

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.rightMap_comp export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (rightMap_comp)


/-- 同じ関手的分解と元の中間射の pushout による左脚の置換。 -/
def obj (S : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y where
  left := intermediate cof S
  right := right cof S
  leftMap := last cof S
  middle := inl cof S
  rightMap := S.rightMap ≫ inr cof S
  left_mem := cof.hp _
  right_mem := (weakEquivalences C).comp_mem _ _ S.right_mem (inr_trivialCofibration cof S).2

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.obj export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (obj)


def map {S T : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y} (f : S ⟶ T) : obj cof S ⟶ obj cof T where
  left := intermediateMap cof f
  right := rightMap cof f
  left_w := map_last cof f
  middle_w := inl_rightMap cof f
  right_w := by
    change (S.rightMap ≫ inr cof S) ≫ rightMap cof f = T.rightMap ≫ inr cof T
    rw [Category.assoc, inr_rightMap, ← Category.assoc, f.right_w]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.map export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (map)


/-- 元の全対象・全射の左脚を関手的に置き換える。 -/
def functor : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y where
  obj := obj cof
  map := map cof
  map_id S := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext
    · change cof.Z.map (arrowMap (𝟙 S)) = 𝟙 _
      rw [arrowMap_id, cof.Z.map_id]
    · exact rightMap_id cof S
  map_comp f g := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext
    · change cof.Z.map (arrowMap (f ≫ g)) = cof.Z.map (arrowMap f) ≫ cof.Z.map (arrowMap g)
      rw [arrowMap_comp, cof.Z.map_comp]
    · exact rightMap_comp cof f g

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.functor export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (functor)


/-- 元の自明 cofibration と pushout の包含による、元の三本矢からの自然変換。 -/
def unit : 𝟭 (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y) ⟶ functor cof ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.leftInclusion where
  app S :=
    { left := first cof S
      right := inr cof S
      left_w := fac cof S
      middle_w := pushout.condition.symm
      right_w := rfl }
  naturality _ _ f := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext _ _ (map_first cof f) (inr_rightMap cof f).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.unit export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (unit)


include cof in
/-- 同じ元の左脚の包含の nerve は、関手的置換の単位から反転される。 -/
lemma inclusion_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.leftInclusion : _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.LeftTrivialThreeArrow X Y ⥤ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow X Y))) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FullyFaithfulNerveRetraction.of_unit _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.leftInclusion (functor cof) (unit cof)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.WeakThreeArrow.LeftReplacement.inclusion_localized_isIso export _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement (inclusion_localized_isIso)


end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ThreeArrowLeftReplacement
