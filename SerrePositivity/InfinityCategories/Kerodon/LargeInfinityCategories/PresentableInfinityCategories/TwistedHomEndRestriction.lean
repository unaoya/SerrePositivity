module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.TwistedHomEndSection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.TwistedHomFunctorMap

/-!
概要：end の実切断比較を関手の始域の制限と可換にする。
方針：twisted Hom の前合成と end 切断の pullback を、普遍評価の同じ射で比較する。
規約：元の F・G と任意の始域の射を保持する。
使われ方：単体分解に沿って end 比較の同値性を検証する制限正方形。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：二関手の end の底写像は任意の始域の制限と可換。
方針：twisted arrow の左右の射影の自然性を両成分に使う。
規約：同型を介さない射の等式。使われ方：制限した係数の全空間の同定。 -/
lemma functorEndPairBase_precomp {A B C : SSet.{u}} (f : B ⟶ A) (F G : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndPairBase F G =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndPairBase (f ≫ F) (f ≫ G) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：始域の制限が元の関手圏の twisted Hom に誘導する射。
方針：内部 Hom の前合成を twisted Hom の両端に適用する。
規約：元の F と G の制限を始点・終点に取る。
使われ方：end 比較の制限正方形の上辺。 -/
def twistedFunctorHomRestriction {A B C : SSet.{u}} (f : B ⟶ A) (F G : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ G)) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.twistedHomFunctorMap ((pre f).app C) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)

/-- 概要：twisted Hom の恒等制限は恒等射。
方針：fiber の包含後に内部 Hom の恒等前合成を計算する。
規約：元の端点を保持する。使われ方：制限図式の関手の単位則。 -/
lemma twistedFunctorHomRestriction_id {A C : SSet.{u}} (F G : A ⟶ C) :
    twistedFunctorHomRestriction (𝟙 A) F G = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change s.val ≫ (pre (𝟙 A)).app C = s.val
  rw [pre_id, NatTrans.id_app, Category.comp_id]

/-- 概要：twisted Hom の二段の制限は合成射による制限。
方針：fiber の包含後に内部 Hom の前合成の合成則を使う。
規約：元の単体集合の合成を使う。使われ方：制限図式の関手の合成則。 -/
lemma twistedFunctorHomRestriction_comp {A B D C : SSet.{u}}
    (f : B ⟶ A) (g : D ⟶ B) (F G : A ⟶ C) :
    twistedFunctorHomRestriction f F G ≫ twistedFunctorHomRestriction g (f ≫ F) (f ≫ G) =
      twistedFunctorHomRestriction (g ≫ f) F G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  change (s.val ≫ (pre f).app C) ≫ (pre g).app C = s.val ≫ (pre (g ≫ f)).app C
  rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]

/-- 概要：普遍的な twisted Hom の評価は始域の制限と厳密に可換。
方針：同じ edgewise 重み上の二変数評価を各次数で比較する。
規約：全ての変換パラメーターを保持する。使われ方：切断比較の自然性。 -/
lemma twistedFunctorHomEvaluation_precomp {A B C : SSet.{u}}
    (f : B ⟶ A) (F G : A ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow B ◁ twistedFunctorHomRestriction f F G) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomEvaluation (f ≫ F) (f ≫ G) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowHomSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomEvaluation F G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, s⟩
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro t
  rfl

/-- 概要：end の切断を始域で制限する普遍的な評価。
方針：切断を twisted arrow の写像で前合成し、制限した底の pullback へ持ち上げる。
規約：指定された実切断を保持する。使われ方：end 切断の制限射の uncurry。 -/
def functorEndSectionsRestrictionEvaluation {A B C : SSet.{u}}
    (f : B ⟶ A) (F G : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow B ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndTotal (f ≫ F) (f ≫ G) :=
  pullback.lift
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f ▷ _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G) ≫
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndPairBase F G))
    (fst _ _) (by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation _) _ _]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f ▷ _) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndPairBase F G = _
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation_projection,
        whiskerRight_fst_assoc, functorEndPairBase_precomp])

/-- 概要：制限した end の普遍評価の全空間成分。
方針：pullback の第一射影則を使う。
規約：元の合成の括弧を保持する。使われ方：制限の合成則。 -/
lemma functorEndSectionsRestrictionEvaluation_fst {A B C : SSet.{u}}
    (f : B ⟶ A) (F G : A ⟶ C) :
    functorEndSectionsRestrictionEvaluation f F G ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndPairBase (f ≫ F) (f ≫ G)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f ▷ _) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G) ≫
        pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndPairBase F G) :=
  pullback.lift_fst _ _ _

/-- 概要：制限した end の普遍評価の底成分は第一因子の射影。
方針：pullback の第二射影則を使う。
規約：元の切断パラメーターを保持する。使われ方：制限の合成則。 -/
lemma functorEndSectionsRestrictionEvaluation_snd {A B C : SSet.{u}}
    (f : B ⟶ A) (F G : A ⟶ C) :
    functorEndSectionsRestrictionEvaluation f F G ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection (f ≫ F) (f ≫ G) = fst _ _ :=
  pullback.lift_snd _ _ _

/-- 概要：end 係数の切断空間の始域に関する制限射。
方針：制限した普遍評価を切断空間の表現性で curry する。
規約：制限した二関手の実 pullback の切断を取る。
使われ方：end 比較の制限正方形の下辺。 -/
def functorEndSectionsRestriction {A B C : SSet.{u}} (f : B ⟶ A) (F G : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection (f ≫ F) (f ≫ G)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift (functorEndSectionsRestrictionEvaluation f F G)
    (pullback.lift_snd _ _ _)

/-- 概要：制限した切断を評価すると元の切断の制限に戻る。
方針：切断空間への持ち上げの普遍評価則を使う。
規約：全パラメーターの等式。使われ方：比較の制限正方形の検証。 -/
lemma functorEndSectionsRestriction_evaluation {A B C : SSet.{u}}
    (f : B ⟶ A) (F G : A ⟶ C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow B ◁ functorEndSectionsRestriction f F G) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection (f ≫ F) (f ≫ G)) =
        functorEndSectionsRestrictionEvaluation f F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsLift_evaluation _ _

/-- 概要：end の実比較射は始域の制限について自然。
方針：切断の普遍評価で検出し、twisted Hom の評価の制限則へ戻す。
規約：同型でなく元の写像の可換正方形。使われ方：単体分解に沿う同値性の検証。 -/
lemma twistedFunctorHomToEndSections_precomp {A B C : SSet.{u}}
    (f : B ⟶ A) (F G : A ⟶ C) :
    twistedFunctorHomRestriction f F G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomToEndSections (f ≫ F) (f ≫ G) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomToEndSections F G ≫ functorEndSectionsRestriction f F G := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
  simp only [whiskerLeft_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomToEndSections_evaluation, functorEndSectionsRestriction_evaluation]
  apply pullback.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomEndEvaluation,
      functorEndSectionsRestrictionEvaluation, pullback.lift_fst]
    rw [← Category.assoc, whisker_exchange, Category.assoc,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow A ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomToEndSections F G),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomToEndSections_evaluation]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomEndEvaluation, pullback.lift_fst]
    exact twistedFunctorHomEvaluation_precomp f F G
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.twistedFunctorHomEndEvaluation,
      functorEndSectionsRestrictionEvaluation, pullback.lift_snd, whiskerLeft_fst]

/-- 概要：end 切断の恒等制限は恒等射。
方針：普遍評価の二つの pullback 射影で等式を検出する。
規約：元の実切断を保持する。使われ方：切断制限図式の単位則。 -/
lemma functorEndSectionsRestriction_id {A C : SSet.{u}} (F G : A ⟶ C) :
    functorEndSectionsRestriction (𝟙 A) F G = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
  rw [functorEndSectionsRestriction_evaluation]
  change functorEndSectionsRestrictionEvaluation (𝟙 A) F G =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G)
  apply pullback.hom_ext
  · simp only [functorEndSectionsRestrictionEvaluation, pullback.lift_fst]
    rfl
  · rw [functorEndSectionsRestrictionEvaluation, pullback.lift_snd]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G)).symm

/-- 概要：end 切断の二段の制限は合成射による制限。
方針：普遍評価と二つの射影で検出し、第一因子の前合成を合成する。
規約：単射性を仮定しない。使われ方：単体分解の切断制限図式の合成則。 -/
lemma functorEndSectionsRestriction_comp {A B D C : SSet.{u}}
    (f : B ⟶ A) (g : D ⟶ B) (F G : A ⟶ C) :
    functorEndSectionsRestriction f F G ≫ functorEndSectionsRestriction g (f ≫ F) (f ≫ G) =
      functorEndSectionsRestriction (g ≫ f) F G := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSections_hom_ext
  calc
    _ = functorEndSectionsRestrictionEvaluation (g ≫ f) F G := by
      simp only [whiskerLeft_comp, Category.assoc,
        functorEndSectionsRestriction_evaluation g (f ≫ F) (f ≫ G)]
      apply pullback.hom_ext
      · trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap (g ≫ f) ▷ _) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.simplicialSectionsEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection F G) ≫
            pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.twistedArrowProjection C) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndPairBase F G)
        · rw [Category.assoc, functorEndSectionsRestrictionEvaluation_fst,
            ← Category.assoc, whisker_exchange, Category.assoc,
            ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow B ◁ functorEndSectionsRestriction f F G),
            functorEndSectionsRestriction_evaluation,
            functorEndSectionsRestrictionEvaluation_fst]
          rw [← Category.assoc, ← comp_whiskerRight]
          rfl
        · exact (functorEndSectionsRestrictionEvaluation_fst (g ≫ f) F G).symm
      · trans fst _ _
        · change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow D ◁ functorEndSectionsRestriction f F G) ≫
            functorEndSectionsRestrictionEvaluation g (f ≫ F) (f ≫ G) ≫
              _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorEndProjection (g ≫ (f ≫ F)) (g ≫ (f ≫ G)) = _
          rw [functorEndSectionsRestrictionEvaluation_snd, whiskerLeft_fst]
        · exact (functorEndSectionsRestrictionEvaluation_snd (g ≫ f) F G).symm
    _ = _ := (functorEndSectionsRestriction_evaluation (g ≫ f) F G).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
