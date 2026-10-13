module

public import SerrePositivity.Spectra.SymmetricSequence.DaySymmetry
public import Mathlib.CategoryTheory.Monoidal.DayConvolution.Closed

/-!
# convolution の内部 Hom の end による構成

各添字 x において、j に関する基礎圏の内部 Hom `[F(j), G(j ⊕ x)]` の end を取る。
置換に関する条件を end の普遍性へ組み込み、x と G についての関手性を構成する。
convolution との随伴と閉構造の型クラス登録は `DayAdjunction` でこのデータから導く。
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

/-- 内部 Hom を計算する各次数の二変数図式。 -/
def internalHomDiagram (F G : SymmetricSequence C) (x : FiniteBijection) :
    FiniteBijectionᵒᵖ ⥤ FiniteBijection ⥤ C :=
  ((dayConvolutionInternalHomDiagramFunctor (toFunctorCategory.obj F)).obj
    (toFunctorCategory.obj G)).obj x

/-- end による内部 Hom の候補。 -/
def internalHomFunctor (F : SymmetricSequence C) : SymmetricSequence C ⥤ SymmetricSequence C :=
  toFunctorCategory ⋙ dayConvolutionInternalHomDiagramFunctor (toFunctorCategory.obj F) ⋙
    (Functor.whiskeringRight _ _ _).obj (endFunctor FiniteBijection C) ⋙ fromFunctorCategory

/-- 各次数の対象は、指定した図式の end そのもの。 -/
lemma internalHomFunctor_obj_obj (F G : SymmetricSequence C) (x : FiniteBijection) :
    ((internalHomFunctor F).obj G).obj x = end_ (internalHomDiagram F G x) := rfl

/-- end から各内部 Hom への標準射。 -/
def internalHomProjection (F G : SymmetricSequence C) (x j : FiniteBijection) :
    ((internalHomFunctor F).obj G).obj x ⟶ (ihom (F.obj j)).obj (G.obj (j ⊗ x)) :=
  end_.π (internalHomDiagram F G x) j

/-- end の射は、置換の引き戻しと行き先への作用を同一視する。 -/
lemma internalHomProjection_condition (F G : SymmetricSequence C) (x : FiniteBijection)
    {i j : FiniteBijection} (f : i ⟶ j) :
    internalHomProjection F G x i ≫ (ihom (F.obj i)).map (G.map (f ▷ x)) =
      internalHomProjection F G x j ≫ (MonoidalClosed.pre (F.map f)).app (G.obj (j ⊗ x)) := by
  exact end_.condition (internalHomDiagram F G x) f

/-- この end は Day 内部 Hom の普遍性と添字の関手性を備える。 -/
def dayInternalHom (F G : SymmetricSequence C) :
    DayConvolutionInternalHom (toFunctorCategory.obj F) (toFunctorCategory.obj G)
      (toFunctorCategory.obj ((internalHomFunctor F).obj G)) where
  π := internalHomProjection F G
  hπ := by
    intro x i j f
    exact internalHomProjection_condition F G x f
  isLimitWedge x := by
    exact IsLimit.ofIsoLimit (limit.isLimit _) (Wedge.ext (Iso.refl _) (fun j ↦ by
      simp [internalHomProjection, internalHomDiagram, end_.π]))
  map_comp_π f j := by
    exact end_.map_π _ j

variable [HasColimitsOfSize.{0, 0} C]

/-- end の射影と convolution の普遍性から得る評価射。 -/
def internalHomEvaluation (F G : SymmetricSequence C) :
    convolution F ((internalHomFunctor F).obj G) ⟶ G := by
  letI : DayConvolution (toFunctorCategory.obj F)
      (toFunctorCategory.obj ((internalHomFunctor F).obj G)) :=
    dayConvolution F ((internalHomFunctor F).obj G)
  exact (dayInternalHom F G).ev_app

/-- convolution の構造射を curry して end へ送る余評価射。 -/
def internalHomCoevaluation (F G : SymmetricSequence C) :
    G ⟶ (internalHomFunctor F).obj (convolution F G) := by
  letI : DayConvolution (toFunctorCategory.obj F) (toFunctorCategory.obj G) :=
    dayConvolution F G
  exact DayConvolutionInternalHom.coev_app
    (F := toFunctorCategory.obj F) (G := toFunctorCategory.obj G)
    (H := toFunctorCategory.obj ((internalHomFunctor F).obj (convolution F G)))
    (dayInternalHom F (convolution F G))

end SerrePositivity.SymmetricSequence
