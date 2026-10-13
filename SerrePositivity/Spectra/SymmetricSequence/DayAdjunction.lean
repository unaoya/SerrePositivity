module

public import SerrePositivity.Spectra.SymmetricSequence.DayInternalHom

/-!
# convolution と end による内部 Hom の随伴

end の誘導射を内部 Hom 関手の写像と比較する。
lawful な Day 構造に沿った評価・余評価を用いて自然性と三角恒等式を接続する。
-/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [HasLimitsOfSize.{0, 0} C]

/-- 内部 Hom 関手の写像は、Day 内部 Hom の普遍性による誘導射と同じ。 -/
lemma internalHomFunctor_map_eq_dayMap (F : SymmetricSequence C)
    {G G' : SymmetricSequence C} (η : G ⟶ G') :
    toFunctorCategory.map ((internalHomFunctor F).map η) =
      (dayInternalHom F G).map (toFunctorCategory.map η) (dayInternalHom F G') := by
  apply NatTrans.ext
  funext x
  apply Wedge.IsLimit.hom_ext ((dayInternalHom F G').isLimitWedge x)
  intro j
  simp only [Wedge.mk_ι]
  rw [DayConvolutionInternalHom.map_app_comp_π]
  exact end_.map_π (F := internalHomDiagram F G x) (F' := internalHomDiagram F G' x)
    (((dayConvolutionInternalHomDiagramFunctor (toFunctorCategory.obj F)).map
      (toFunctorCategory.map η)).app x) j

variable [SymmetricCategory C] [HasColimitsOfSize.{0, 0} C]

attribute [local instance] LawfulDayConvolutionMonoidalCategoryStruct.convolution
  LawfulDayConvolutionMonoidalCategoryStruct.convolution₂
  LawfulDayConvolutionMonoidalCategoryStruct.convolution₂'

lemma dayEmbedding_map_internalHomFunctor_map (F : SymmetricSequence C)
    {G G' : SymmetricSequence C} (η : G ⟶ G') :
    dayEmbedding.map ((internalHomFunctor F).map η) =
      (dayInternalHom F G).map (dayEmbedding.map η) (dayInternalHom F G') :=
  internalHomFunctor_map_eq_dayMap F η

@[instance_reducible]
def canonicalDayConvolution (F G : SymmetricSequence C) :
    DayConvolution (toFunctorCategory.obj F) (toFunctorCategory.obj G) :=
  LawfulDayConvolutionMonoidalCategoryStruct.convolution
    FiniteBijection C (SymmetricSequence C) F G

attribute [local instance] canonicalDayConvolution

/-- 登録したテンソル積の Day 構造に沿う評価射。 -/
def convolutionEvaluation (F G : SymmetricSequence C) :
    F ⊗ (internalHomFunctor F).obj G ⟶ G :=
  DayConvolutionInternalHom.ev_app
    (F := dayEmbedding.obj F) (G := dayEmbedding.obj G)
    (H := dayEmbedding.obj ((internalHomFunctor F).obj G)) (dayInternalHom F G)

/-- 登録したテンソル積の Day 構造に沿う余評価射。 -/
def convolutionCoevaluation (F G : SymmetricSequence C) :
    G ⟶ (internalHomFunctor F).obj (F ⊗ G) :=
  DayConvolutionInternalHom.coev_app
    (F := dayEmbedding.obj F) (G := dayEmbedding.obj G)
    (H := dayEmbedding.obj ((internalHomFunctor F).obj (F ⊗ G)))
    (dayInternalHom F (F ⊗ G))

@[simp] lemma dayEmbedding_map_evaluation (F G : SymmetricSequence C) :
    dayEmbedding.map (convolutionEvaluation F G) =
      DayConvolutionInternalHom.ev_app (F := dayEmbedding.obj F)
        (G := dayEmbedding.obj G) (H := dayEmbedding.obj ((internalHomFunctor F).obj G))
        (dayInternalHom F G) := rfl

@[simp] lemma dayEmbedding_map_coevaluation (F G : SymmetricSequence C) :
    dayEmbedding.map (convolutionCoevaluation F G) =
      DayConvolutionInternalHom.coev_app (F := dayEmbedding.obj F)
        (G := dayEmbedding.obj G)
        (H := dayEmbedding.obj ((internalHomFunctor F).obj (F ⊗ G)))
        (dayInternalHom F (F ⊗ G)) := rfl

/-- 評価射は行き先に関して自然。 -/
lemma convolutionEvaluation_naturality (F : SymmetricSequence C)
    {G G' : SymmetricSequence C} (η : G ⟶ G') :
    F ◁ (internalHomFunctor F).map η ≫ convolutionEvaluation F G' =
      convolutionEvaluation F G ≫ η := by
  apply (dayEmbedding (C := C)).map_injective
  simp only [Functor.map_comp, ← id_tensorHom,
    LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom,
    dayEmbedding_map_evaluation]
  rw [dayEmbedding_map_internalHomFunctor_map]
  exact DayConvolutionInternalHom.ev_naturality_app
    (dayInternalHom F G) (dayInternalHom F G') (dayEmbedding.map η)

/-- 余評価射は入力に関して自然。 -/
lemma convolutionCoevaluation_naturality (F : SymmetricSequence C)
    {G G' : SymmetricSequence C} (η : G ⟶ G') :
    η ≫ convolutionCoevaluation F G' =
      convolutionCoevaluation F G ≫ (internalHomFunctor F).map (F ◁ η) := by
  apply (dayEmbedding (C := C)).map_injective
  simp only [Functor.map_comp, dayEmbedding_map_coevaluation]
  rw [dayEmbedding_map_internalHomFunctor_map]
  simp only [← id_tensorHom,
    LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom]
  exact DayConvolutionInternalHom.coev_naturality_app
    (F := toFunctorCategory.obj F) (G := toFunctorCategory.obj G)
    (G' := toFunctorCategory.obj G')
    (H := toFunctorCategory.obj ((internalHomFunctor F).obj (F ⊗ G)))
    (H' := toFunctorCategory.obj ((internalHomFunctor F).obj (F ⊗ G')))
    (dayInternalHom F (F ⊗ G)) (dayEmbedding.map η) (dayInternalHom F (F ⊗ G'))

/-- convolution 側の随伴の三角恒等式。 -/
lemma convolutionEvaluation_coevaluation (F G : SymmetricSequence C) :
    F ◁ convolutionCoevaluation F G ≫ convolutionEvaluation F (F ⊗ G) = 𝟙 (F ⊗ G) := by
  apply (dayEmbedding (C := C)).map_injective
  simp only [Functor.map_comp, ← id_tensorHom,
    LawfulDayConvolutionMonoidalCategoryStruct.ι_map_tensorHom_hom_eq_tensorHom,
    dayEmbedding_map_evaluation, dayEmbedding_map_coevaluation]
  rw [(dayEmbedding (C := C)).map_id F, (dayEmbedding (C := C)).map_id (F ⊗ G)]
  simpa only [dayEmbedding, toFunctorCategory, DayConvolution.convolution,
    canonicalDayConvolution, LawfulDayConvolutionMonoidalCategoryStruct.convolution] using
    DayConvolutionInternalHom.left_triangle_components (F := dayEmbedding.obj F)
    (H := dayEmbedding.obj ((internalHomFunctor F).obj (F ⊗ G)))
    (dayEmbedding.obj G) (dayInternalHom F (F ⊗ G))

/-- 内部 Hom 側の随伴の三角恒等式。 -/
lemma convolutionCoevaluation_evaluation (F G : SymmetricSequence C) :
    convolutionCoevaluation F ((internalHomFunctor F).obj G) ≫
      (internalHomFunctor F).map (convolutionEvaluation F G) =
        𝟙 ((internalHomFunctor F).obj G) := by
  apply (dayEmbedding (C := C)).map_injective
  simp only [Functor.map_comp, dayEmbedding_map_coevaluation]
  rw [dayEmbedding_map_internalHomFunctor_map]
  simp only [dayEmbedding_map_evaluation]
  rw [(dayEmbedding (C := C)).map_id ((internalHomFunctor F).obj G)]
  simpa only [dayEmbedding, toFunctorCategory] using
    DayConvolutionInternalHom.right_triangle_components (F := dayEmbedding.obj F)
    (H := dayEmbedding.obj ((internalHomFunctor F).obj G))
    (H' := dayEmbedding.obj ((internalHomFunctor F).obj (F ⊗ (internalHomFunctor F).obj G)))
    (dayEmbedding.obj G) (dayInternalHom F G)
    (dayInternalHom F (F ⊗ (internalHomFunctor F).obj G))

/-- end の内部 Hom を右随伴とする convolution の随伴。 -/
def convolutionHomAdjunction (F : SymmetricSequence C) :
    tensorLeft F ⊣ internalHomFunctor F :=
  Adjunction.mkOfUnitCounit {
    unit := {
      app G := convolutionCoevaluation F G
      naturality := by
        intro G G' η
        exact convolutionCoevaluation_naturality F η }
    counit := {
      app G := convolutionEvaluation F G
      naturality := by
        intro G G' η
        exact convolutionEvaluation_naturality F η }
    left_triangle := by
      apply NatTrans.ext
      funext G
      simpa using convolutionEvaluation_coevaluation F G
    right_triangle := by
      apply NatTrans.ext
      funext G
      simpa using convolutionCoevaluation_evaluation F G }

/-- convolution の閉構造。右随伴は構成した end の関手。 -/
instance convolutionMonoidalClosed : MonoidalClosed (SymmetricSequence C) where
  closed F := {
    rightAdj := internalHomFunctor F
    adj := convolutionHomAdjunction F }

/-- 登録した内部 Hom の各段は、構成した end と同じ。 -/
lemma ihom_obj_obj_eq_end (F G : SymmetricSequence C) (x : FiniteBijection) :
    ((ihom F).obj G).obj x = end_ (internalHomDiagram F G x) := rfl

/-- Mathlib の評価射は構成した convolution の評価射。 -/
lemma ihom_ev_app_eq_convolutionEvaluation (F G : SymmetricSequence C) :
    (ihom.ev F).app G = convolutionEvaluation F G := rfl

/-- Mathlib の余評価射は構成した convolution の余評価射。 -/
lemma ihom_coev_app_eq_convolutionCoevaluation (F G : SymmetricSequence C) :
    (ihom.coev F).app G = convolutionCoevaluation F G := rfl

end SerrePositivity.SymmetricSequence
