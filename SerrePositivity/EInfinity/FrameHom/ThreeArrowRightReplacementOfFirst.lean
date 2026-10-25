module

public import SerrePositivity.EInfinity.FrameHom.ThreeArrowRightReplacement
public import SerrePositivity.EInfinity.FrameHom.SpecialThreeArrowComparison

/-!
概要：元の特殊三本矢比較を第一の関手的分解だけで構成する。
方針：弱な右脚の cofibration・trivial fibration 分解で左射も弱いと二対三から示す。
規約：元の包含と全余単位を保持し、第二分解は仮定しない。
使われ方：関手的 cofibrant 置換と指定 right frame だけを持つ一般モデルの比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacementOfFirst
open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open RightReplacement (arrow arrowMap arrowMap_id arrowMap_comp)
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  {X Y : C}

abbrev intermediate (S : LeftTrivialThreeArrow X Y) : C := cof.Z.obj (arrow S)
abbrev first (S : LeftTrivialThreeArrow X Y) : Y ⟶ intermediate cof S := cof.i.app (arrow S)
abbrev last (S : LeftTrivialThreeArrow X Y) : intermediate cof S ⟶ S.right :=
  cof.p.app (arrow S)
abbrev intermediateMap {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) := cof.Z.map (arrowMap f)

lemma fac (S : LeftTrivialThreeArrow X Y) : first cof S ≫ last cof S = S.rightMap :=
  congr_app cof.fac (arrow S)

lemma map_first {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) :
    first cof S ≫ intermediateMap cof f = first cof T := by
  have h := cof.i.naturality (arrowMap f)
  exact h.symm.trans (Category.id_comp _)

lemma map_last {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) :
    intermediateMap cof f ≫ last cof T = last cof S ≫ f.right :=
  cof.p.naturality (arrowMap f)

/-- 概要：元の弱な右脚の第一分解の左射は自明 cofibration。
方針：元の右脚と右の自明 fibration の二対三を使う。
規約：第一の関手的分解のみ。使われ方：特殊な三本矢の右脚。 -/
lemma first_trivialCofibration (S : LeftTrivialThreeArrow X Y) :
    trivialCofibrations C (first cof S) := by
  refine ⟨cof.hi _, ?_⟩
  apply (weakEquivalences C).of_postcomp _ (last cof S) (cof.hp _).2
  exact (fac cof S).symm ▸ S.right_mem

/-- 概要：同じ第一分解の右射は元の自明 fibration。
方針：同じ関手的分解の右類を読む。
規約：元の分解。使われ方：中間射の pullback の持ち上げ。 -/
lemma last_trivialFibration (S : LeftTrivialThreeArrow X Y) :
    trivialFibrations C (last cof S) := cof.hp _

abbrev left (S : LeftTrivialThreeArrow X Y) : C := pullback S.middle (last cof S)
abbrev fst (S : LeftTrivialThreeArrow X Y) : left cof S ⟶ S.left := pullback.fst _ _
abbrev snd (S : LeftTrivialThreeArrow X Y) : left cof S ⟶ intermediate cof S := pullback.snd _ _

lemma fst_trivialFibration (S : LeftTrivialThreeArrow X Y) :
    trivialFibrations C (fst cof S) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback S.middle (last cof S)).flip
    (last_trivialFibration cof S)

def leftMap {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) : left cof S ⟶ left cof T :=
  pullback.map S.middle (last cof S) T.middle (last cof T)
    f.left (intermediateMap cof f) f.right f.middle_w (map_last cof f).symm

lemma leftMap_fst {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) :
    leftMap cof f ≫ fst cof T = fst cof S ≫ f.left := pullback.lift_fst _ _ _

lemma leftMap_snd {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) :
    leftMap cof f ≫ snd cof T = snd cof S ≫ intermediateMap cof f := pullback.lift_snd _ _ _

lemma leftMap_id (S : LeftTrivialThreeArrow X Y) : leftMap cof (𝟙 S) = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [leftMap_fst]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · rw [leftMap_snd]
    change snd cof S ≫ cof.Z.map (arrowMap (𝟙 S)) = 𝟙 _ ≫ snd cof S
    rw [arrowMap_id, cof.Z.map_id, Category.comp_id, Category.id_comp]

lemma leftMap_comp {S T U : LeftTrivialThreeArrow X Y} (f : S ⟶ T) (g : T ⟶ U) :
    leftMap cof (f ≫ g) = leftMap cof f ≫ leftMap cof g := by
  apply pullback.hom_ext
  · rw [leftMap_fst, Category.assoc, leftMap_fst, ← Category.assoc, leftMap_fst]
    exact (Category.assoc _ _ _).symm
  · rw [leftMap_snd, Category.assoc, leftMap_snd, ← Category.assoc, leftMap_snd]
    change _ ≫ cof.Z.map (arrowMap (f ≫ g)) = (_ ≫ cof.Z.map (arrowMap f)) ≫
      cof.Z.map (arrowMap g)
    rw [arrowMap_comp, cof.Z.map_comp, Category.assoc]

/-- 概要：第一分解と元の中間射の pullback による特殊な三本矢。
方針：同じ右脚の二対三と pullback を使う。規約：元の両端点。
使われ方：同じ特殊三本矢への実関手。 -/
def obj (S : LeftTrivialThreeArrow X Y) : SpecialHammock X Y where
  left := left cof S
  right := intermediate cof S
  leftMap := fst cof S ≫ S.leftMap
  middle := snd cof S
  rightMap := first cof S
  left_mem := (trivialFibrations C).comp_mem _ _ (fst_trivialFibration cof S) S.left_mem
  right_mem := first_trivialCofibration cof S

def map {S T : LeftTrivialThreeArrow X Y} (f : S ⟶ T) : obj cof S ⟶ obj cof T where
  left := leftMap cof f
  right := intermediateMap cof f
  left_w := by
    change leftMap cof f ≫ (fst cof T ≫ T.leftMap) = fst cof S ≫ S.leftMap
    rw [← Category.assoc, leftMap_fst, Category.assoc, f.left_w]
  middle_w := (leftMap_snd cof f).symm
  right_w := map_first cof f

/-- 概要：元の全右脚を第一分解で関手的に置き換える。
方針：同じ pullback の元の射を使う。規約：全対象・全射。
使われ方：包含の実相対逆。 -/
def functor : LeftTrivialThreeArrow X Y ⥤ SpecialHammock X Y where
  obj := obj cof
  map := map cof
  map_id S := by
    apply ArrowSpan.hom_ext
    · exact leftMap_id cof S
    · change cof.Z.map (arrowMap (𝟙 S)) = 𝟙 _
      rw [arrowMap_id, cof.Z.map_id]
  map_comp f g := by
    apply ArrowSpan.hom_ext
    · exact leftMap_comp cof f g
    · change cof.Z.map (arrowMap (f ≫ g)) = cof.Z.map (arrowMap f) ≫ cof.Z.map (arrowMap g)
      rw [arrowMap_comp, cof.Z.map_comp]

/-- 概要：同じ pullback 射影から元の三本矢への自然変換。
方針：同じ二つの射影を全対象で束ねる。規約：元の全自然性。
使われ方：元の包含の nerve の反転。 -/
def counit : functor cof ⋙ specialInclusion ⟶ 𝟭 (LeftTrivialThreeArrow X Y) where
  app S :=
    { left := fst cof S
      right := last cof S
      left_w := rfl
      middle_w := pullback.condition.symm
      right_w := fac cof S }
  naturality _ _ f := ArrowSpan.hom_ext _ _ (leftMap_fst cof f) (map_last cof f)

include cof in
/-- 概要：同じ特殊三本矢の包含の nerve は第一分解で反転。
方針：同じ実余単位と元の充満忠実性を使う。規約：第二分解不要。
使われ方：一般モデル圏の frame 比較の入力削減。 -/
lemma inclusion_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (specialInclusion : SpecialHammock X Y ⥤ LeftTrivialThreeArrow X Y))) :=
  FullyFaithfulNerveRetraction.of_counit specialInclusion (functor cof) (counit cof)

end SerrePositivity.EInfinity.FrameHom.WeakThreeArrow.RightReplacementOfFirst

namespace SerrePositivity.EInfinity.FrameHom.WeakThreeArrow
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

include cof in
/-- 概要：元の特殊三本矢の包含は第一分解だけで反転する。
方針：左脚の既存置換と右脚の第一分解による置換を合成する。
規約：第二の関手的分解を仮定しない。使われ方：一般の実 frame 比較。 -/
lemma inclusion_localized_isIso_of_first (X Y : C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (inclusion X Y))) := by
  have := LeftReplacement.inclusion_localized_isIso cof (X := X) (Y := Y)
  have := RightReplacementOfFirst.inclusion_localized_isIso cof (X := X) (Y := Y)
  rw [← inclusion_fac]
  change IsIso (AnodyneHomotopy.anodyneQ.map
    (nerveMap (specialInclusion : SpecialHammock X Y ⥤ LeftTrivialThreeArrow X Y) ≫
      nerveMap leftInclusion))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

include cof in
/-- 概要：元の特殊三本矢の包含の実射は第一分解だけで弱同値。
方針：同じ反転性を全 Kan 標的で検出する。
規約：単体集合モデルは不要。使われ方：全源 frame の reduced 比較。 -/
lemma inclusion_isWeakHomotopyEquivalence_of_first (X Y : C) :
    IsWeakHomotopyEquivalence (nerveMap (inclusion X Y)) :=
  AnodyneWeakDetection.isWeakHomotopyEquivalence _ (inclusion_localized_isIso_of_first cof X Y)

end SerrePositivity.EInfinity.FrameHom.WeakThreeArrow
