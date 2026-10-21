module

public import SerrePositivity.EInfinity.Hammock.FirstColumnBackwardBackwardData

/-!
# 後向き二列の指定 Hom 係数の恒等・合成則

概要：指定部分圏の元の Hom と端点移送による係数写像の全関手則。
方針：離散圏の対象の等式を元の指定射の合成へ戻す。
規約：同じ指定射と端点表示を保持する。
使われ方：元の二方向係数図式と augmentation の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite SimplicialLocalization
variable {C D E : RelativeCategory.{u}} (w : Word)
lemma backwardBackwardLeftMap_id_heq (F : C ⟶ C) (h : F = 𝟙 C)
    (X Y : C.category) (hX : F.functor.obj X = X) (Z : WideSubcategory C.weakEquivalences) :
    HEq ((backwardBackwardLeftMap (Y := Y) (Y' := Y) w F hX).app (op Z))
      (𝟙 (Cat.of (Discrete (Z ⟶ (⟨X⟩ : WideSubcategory C.weakEquivalences))))) := by
  cases h
  apply heq_of_eq
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext (fun e => Discrete.ext ?_) ?_
  · change e.as ≫ (𝟙 (⟨X⟩ : WideSubcategory C.weakEquivalences)) = e.as
    exact Category.comp_id _
  · intro e e' f
    exact @Discrete.hom_eq (Z ⟶ (⟨X⟩ : WideSubcategory C.weakEquivalences)) _ _ _ _
lemma backwardBackwardLeftMap_comp_heq (F : C ⟶ D) (G : D ⟶ E) (H : C ⟶ E)
    (h : H = F ≫ G) (X Y : C.category) (X' Y' : D.category) (X'' Y'' : E.category)
    (hX : F.functor.obj X = X') (hX' : G.functor.obj X' = X'') (hXH : H.functor.obj X = X'')
    (Z : WideSubcategory C.weakEquivalences) :
    HEq ((backwardBackwardLeftMap (Y := Y) (Y' := Y'') w H hXH).app (op Z))
      (((backwardBackwardLeftMap (Y := Y) (Y' := Y') w F hX).app (op Z)) ≫
        ((backwardBackwardLeftMap (Y := Y') (Y' := Y'') w G hX').app
          (op ((markedCategoryMap F).obj Z)))) := by
  cases h
  apply heq_of_eq
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext (fun e => Discrete.ext ?_) ?_
  · change (markedCategoryMap G).map ((markedCategoryMap F).map e.as) ≫
      eqToHom (congrArg (fun T => (⟨T⟩ : WideSubcategory E.weakEquivalences)) hXH) =
      (markedCategoryMap G).map ((markedCategoryMap F).map e.as ≫
        eqToHom (congrArg (fun T => (⟨T⟩ : WideSubcategory D.weakEquivalences)) hX)) ≫
        eqToHom (congrArg (fun T => (⟨T⟩ : WideSubcategory E.weakEquivalences)) hX')
    simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
  · intro e e' f
    exact @Discrete.hom_eq ((⟨G.functor.obj (F.functor.obj Z.obj)⟩ : WideSubcategory
      E.weakEquivalences) ⟶ ⟨X''⟩) _ _ _ _
end SerrePositivity.EInfinity.Hammock.FirstColumn
