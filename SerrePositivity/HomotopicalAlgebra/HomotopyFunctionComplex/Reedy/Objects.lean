module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.Index
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-! # Latching and matching objects and their relative comparison maps

These are constructed from the actual direct and inverse indexing categories
of a Mathlib Reedy structure. Existence of the particular limits and colimits
is explicit, so the interface also applies to finitely complete model sources.
-/

@[expose] public section
universe v u t v' u'
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.Reedy
variable {J : Type u} [Category.{v} J] {inverse direct : MorphismProperty J}
  [inverse.IsMultiplicative] [direct.IsMultiplicative]
  {α : Type t} [LinearOrder α] [OrderBot α] [SuccOrder α] [WellFoundedLT α]
  (r : ReedyStructure inverse direct α) {C : Type u'} [Category.{v'} C]

abbrev latchingCocone (F : J ⥤ C) (j : J) : Cocone (latchingSource r j ⋙ F) where
  pt := F.obj j
  ι :=
    { app f := F.map f.obj.hom
      naturality f g φ := by
        change F.map φ.hom.left ≫ F.map g.obj.hom = F.map f.obj.hom ≫ 𝟙 _
        rw [← F.map_comp, Over.w, Category.comp_id] }

abbrev matchingCone (F : J ⥤ C) (j : J) : Cone (matchingTarget r j ⋙ F) where
  pt := F.obj j
  π :=
    { app f := F.map f.obj.hom
      naturality f g φ := by
        change 𝟙 _ ≫ F.map g.obj.hom = F.map f.obj.hom ≫ F.map φ.hom.right
        rw [← F.map_comp, Under.w, Category.id_comp] }

variable (j : J)

abbrev latchingEvaluation [HasColimitsOfShape (LatchingIndex r j) C] : (J ⥤ C) ⥤ C :=
  (Functor.whiskeringLeft (LatchingIndex r j) J C).obj (latchingSource r j) ⋙ colim

abbrev matchingEvaluation [HasLimitsOfShape (MatchingIndex r j) C] : (J ⥤ C) ⥤ C :=
  (Functor.whiskeringLeft (MatchingIndex r j) J C).obj (matchingTarget r j) ⋙ lim

def latchingComparison [HasColimitsOfShape (LatchingIndex r j) C] :
    latchingEvaluation r j ⟶ (evaluation J C).obj j where
  app F := colimit.desc _ (latchingCocone r F j)
  naturality F G τ := by
    change colim.map (Functor.whiskerLeft (latchingSource r j) τ) ≫
        colimit.desc _ (latchingCocone r G j) =
      colimit.desc _ (latchingCocone r F j) ≫ τ.app j
    apply colimit.hom_ext
    intro f
    simp only [colimit.ι_map_assoc, colimit.ι_desc, colimit.ι_desc_assoc,
      Functor.whiskerLeft_app]
    exact (τ.naturality f.obj.hom).symm

def matchingComparison [HasLimitsOfShape (MatchingIndex r j) C] :
    (evaluation J C).obj j ⟶ matchingEvaluation r j where
  app F := limit.lift _ (matchingCone r F j)
  naturality F G τ := by
    change τ.app j ≫ limit.lift _ (matchingCone r G j) =
      limit.lift _ (matchingCone r F j) ≫ lim.map (Functor.whiskerLeft (matchingTarget r j) τ)
    apply limit.hom_ext
    intro f
    change (τ.app j ≫ limit.lift _ (matchingCone r G j)) ≫
        limit.π (matchingTarget r j ⋙ G) f =
      (limit.lift _ (matchingCone r F j) ≫
        lim.map (Functor.whiskerLeft (matchingTarget r j) τ)) ≫
          limit.π (matchingTarget r j ⋙ G) f
    rw [Category.assoc, limit.lift_π, Category.assoc, limit.map_π,
      ← Category.assoc, limit.lift_π]
    exact (τ.naturality f.obj.hom).symm

variable {F G : J ⥤ C} (τ : F ⟶ G)

def relativeLatchingMap [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C] :
    pushout ((latchingEvaluation r j).map τ) ((latchingComparison r j).app F) ⟶ G.obj j :=
  pushout.desc ((latchingComparison r j).app G) (τ.app j)
    ((latchingComparison r j).naturality τ)

def relativeMatchingMap [HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C] :
    F.obj j ⟶ pullback ((matchingComparison r j).app G) ((matchingEvaluation r j).map τ) :=
  pullback.lift (τ.app j) ((matchingComparison r j).app F)
    ((matchingComparison r j).naturality τ)

@[reassoc (attr := simp)]
lemma inl_relativeLatchingMap [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C] :
    pushout.inl ((latchingEvaluation r j).map τ) ((latchingComparison r j).app F) ≫
      relativeLatchingMap r j τ = (latchingComparison r j).app G := by
  simp [relativeLatchingMap]

@[reassoc (attr := simp)]
lemma inr_relativeLatchingMap [HasColimitsOfShape (LatchingIndex r j) C] [HasPushouts C] :
    pushout.inr ((latchingEvaluation r j).map τ) ((latchingComparison r j).app F) ≫
      relativeLatchingMap r j τ = τ.app j := by
  simp [relativeLatchingMap]

@[reassoc (attr := simp)]
lemma relativeMatchingMap_fst [HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C] :
    relativeMatchingMap r j τ ≫
      pullback.fst ((matchingComparison r j).app G) ((matchingEvaluation r j).map τ) = τ.app j := by
  simp [relativeMatchingMap]

@[reassoc (attr := simp)]
lemma relativeMatchingMap_snd [HasLimitsOfShape (MatchingIndex r j) C] [HasPullbacks C] :
    relativeMatchingMap r j τ ≫
      pullback.snd ((matchingComparison r j).app G) ((matchingEvaluation r j).map τ) =
        (matchingComparison r j).app F := by
  simp [relativeMatchingMap]

end SerrePositivity.Reedy

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.2.1.1" (partial := special) "仮定：通常圏、Reedy 添字圏と必要な極限・余極限（Lean が強い：通常圏の場合）。結論：latching・matching の評価関手を定義する（通常圏の単体添字に特殊化すると HA の対象の定義に一致）。一般の可呈示 ∞ 圏の構成は含まれない。"] _root_.SerrePositivity.Reedy.latchingEvaluation
attribute [cite HA "7.2.1.1" (partial := special) "仮定：通常圏、Reedy 添字圏と必要な極限・余極限（Lean が強い：通常圏の場合）。結論：latching・matching の評価関手を定義する（通常圏の単体添字に特殊化すると HA の対象の定義に一致）。一般の可呈示 ∞ 圏の構成は含まれない。"] _root_.SerrePositivity.Reedy.matchingEvaluation
attribute [cite HTT "A.2.9.7" (partial := stronger-hyp) "仮定：整列次数付き Reedy 圏と必要な極限・余極限（次数データが Lean で追加）。結論：非恒等直射の over 圏による colimit と非恒等逆射の under 圏による limit、および X(j) との標準射を構成する。二つの定義と射は原典に一致。"] _root_.SerrePositivity.Reedy.latchingComparison
attribute [cite HTT "A.2.9.7" (partial := stronger-hyp) "仮定：整列次数付き Reedy 圏と必要な極限・余極限（次数データが Lean で追加）。結論：非恒等直射の over 圏による colimit と非恒等逆射の under 圏による limit、および X(j) との標準射を構成する。二つの定義と射は原典に一致。"] _root_.SerrePositivity.Reedy.latchingEvaluation
attribute [cite HTT "A.2.9.7" (partial := stronger-hyp) "仮定：整列次数付き Reedy 圏と必要な極限・余極限（次数データが Lean で追加）。結論：非恒等直射の over 圏による colimit と非恒等逆射の under 圏による limit、および X(j) との標準射を構成する。二つの定義と射は原典に一致。"] _root_.SerrePositivity.Reedy.matchingComparison
attribute [cite HTT "A.2.9.7" (partial := stronger-hyp) "仮定：整列次数付き Reedy 圏と必要な極限・余極限（次数データが Lean で追加）。結論：非恒等直射の over 圏による colimit と非恒等逆射の under 圏による limit、および X(j) との標準射を構成する。二つの定義と射は原典に一致。"] _root_.SerrePositivity.Reedy.matchingEvaluation
