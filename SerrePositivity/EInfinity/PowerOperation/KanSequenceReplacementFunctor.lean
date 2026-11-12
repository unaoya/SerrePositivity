module

public import SerrePositivity.EInfinity.PowerOperation.KanSequenceReplacementMaps

/-!
# 既存の逐次単射置換の全関手性

BF 1978 §2 の実際の置換の恒等射・合成の法則。
関手的 SOA の法則を段ごとに使い、比較射も自然変換として保持する。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.KST.Spectra

lemma replacementStageMap_id (X : KanSequence.{u}) (n : ℕ) :
    (replacementStageMap (𝟙 X) n).val = 𝟙 _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change pointedFactorizationFunctor.map
      (replacementInputSquare (𝟙 X) n (replacementStageMap (𝟙 X) n).val
        (replacementStageMap (𝟙 X) n).property) = 𝟙 _
    have h : replacementInputSquare (𝟙 X) n (replacementStageMap (𝟙 X) n).val
        (replacementStageMap (𝟙 X) n).property = 𝟙 _ := by
      apply Arrow.hom_ext
      · simp only [replacementInputSquare, ih, whiskerLeft_id, Arrow.id_left]
        rfl
      · rfl
    rw [h, pointedFactorizationFunctor.map_id]

lemma replacementStageMap_comp {X Y Z : KanSequence.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) :
    (replacementStageMap (f ≫ g) n).val =
      (replacementStageMap f n).val ≫ (replacementStageMap g n).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let sf := replacementInputSquare f n (replacementStageMap f n).val
      (replacementStageMap f n).property
    let sg := replacementInputSquare g n (replacementStageMap g n).val
      (replacementStageMap g n).property
    have h : replacementInputSquare (f ≫ g) n (replacementStageMap (f ≫ g) n).val
        (replacementStageMap (f ≫ g) n).property = sf ≫ sg := by
      apply Arrow.hom_ext
      · change PointedSimplicialSet.circle.{u} ◁
          (replacementStageMap (f ≫ g) n).val =
          (PointedSimplicialSet.circle.{u} ◁ (replacementStageMap f n).val) ≫
            (PointedSimplicialSet.circle.{u} ◁ (replacementStageMap g n).val)
        rw [ih, whiskerLeft_comp]
      · rfl
    change pointedFactorizationFunctor.map
      (replacementInputSquare (f ≫ g) n (replacementStageMap (f ≫ g) n).val
        (replacementStageMap (f ≫ g) n).property) =
      pointedFactorizationFunctor.map sf ≫ pointedFactorizationFunctor.map sg
    rw [h, pointedFactorizationFunctor.map_comp]

/-- 既存の同じ cofibrant 置換は通常の全関手をなす。 -/
def kanSequenceReplacementFunctor : KanSequence.{u} ⥤ KanSequence.{u} where
  obj X := X.cofibrantReplacement
  map f := kanSequenceReplacementMap f
  map_id X := by
    apply KanSequence.Hom.ext_app
    intro n
    exact replacementStageMap_id X n
  map_comp f g := by
    apply KanSequence.Hom.ext_app
    intro n
    exact replacementStageMap_comp f g n

/-- 元の同じ段ごとの比較は全関手間の自然変換。 -/
def kanSequenceReplacementProjection : kanSequenceReplacementFunctor.{u} ⟶
    𝟭 KanSequence.{u} where
  app X := KanSequence.replacementProjection X
  naturality {_X _Y} f := kanSequenceReplacementMap_projection f

/-- 同じ比較自然変換によって、各段の π 同型も置換へ運ばれる。 -/
lemma kanSequenceReplacementMap_piIsomorphism {X Y : KanSequence.{u}} (f : X ⟶ Y)
    (hf : ∀ n, SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (f.app n).right) (n : ℕ) :
    SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      ((kanSequenceReplacementMap f).app n).right := by
  have h := congrArg (fun s : X.cofibrantReplacement ⟶ Y => (s.app n).right)
    (kanSequenceReplacementMap_projection f)
  have hc : SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism
      (((kanSequenceReplacementMap f).app n).right ≫
        ((KanSequence.replacementProjection Y).app n).right) := by
    rw [show ((kanSequenceReplacementMap f).app n).right ≫
      ((KanSequence.replacementProjection Y).app n).right =
      ((KanSequence.replacementProjection X).app n).right ≫ (f.app n).right from h]
    exact (KanSequence.replacementProjection_piIsomorphism X n).comp (hf n)
  exact hc.of_comp (KanSequence.replacementProjection_piIsomorphism Y n)

end SerrePositivity.EInfinity.PowerOperation
