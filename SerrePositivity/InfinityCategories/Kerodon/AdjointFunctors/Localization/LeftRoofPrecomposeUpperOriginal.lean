module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeUpperInsertion
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeUpperDiagram

/-!
# 始域比較の上行を元の frame 比較へ回収する全図式

概要：元の三列の上行は恒等列挿入で四列に、合成で元の roof に戻る。
方針：同じ全対象・全縦射と元の語の作用を使う。
規約：元の比較・中間射・全作用素を保持する。
使われ方：上行の nerve ホモトピーと元の始域作用の照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uI vI
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X' U' U Y : C}

def upperOriginal (p' : U' ⟶ X') (hp' : W p') (α : U' ⟶ U) (σ : U ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postWord X' Y where
  vertex := ![X', U', U, Y]
  first := rfl
  last := rfl
  arrow := Fin.cases p' (Fin.cases α (Fin.cases σ (fun i => Fin.elim0 i)))
  backward_mem i hi := by
    fin_cases i
    · exact hp'
    · cases hi
    · cases hi

omit [W.IsMultiplicative] in
lemma upperOriginal_append (p' : U' ⟶ X') (hp' : W p') (α : U' ⟶ U) (σ : U ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p' hp' α) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj σ) =
      upperOriginal W p' hp' α σ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext
  · intro j
    fin_cases j <;> rfl
  · intro i
    fin_cases i
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p' hp' α)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) σ) (0 : Fin 2)
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_left_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p' hp' α)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) σ) (1 : Fin 2)
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.arrow_right_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W p' hp' α)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) σ) (0 : Fin 1)

variable {I : Type uI} [Category.{vI} I] (A' A : I ⥤ C)
  (p' : A' ⟶ (Functor.const I).obj X') (hp' : ∀ i, W (p'.app i))
  (α : A' ⟶ A) (σ : A ⟶ (Functor.const I).obj Y)
  (hA' : ∀ {i j} (a : i ⟶ j), W (A'.map a))
  (hA : ∀ {i j} (a : i ⟶ j), W (A.map a))

def upperOriginalDiagram : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postWord X' Y where
  obj i := upperOriginal W (p'.app i) (hp' i) (α.app i) (σ.app i)
  map {i j} a :=
    { app := Fin.cases (𝟙 X') (Fin.cases (A'.map a) (Fin.cases (A.map a)
        (Fin.cases (𝟙 Y) (fun k => Fin.elim0 k))))
      app_mem k := by
        fin_cases k
        · exact W.id_mem X'
        · exact hA' a
        · exact hA a
        · exact W.id_mem Y
      first := rfl
      last := rfl
      comm k := by
        fin_cases k
        · exact (p'.naturality a).symm
        · exact (α.naturality a).symm
        · exact (σ.naturality a).symm }
  map_id i := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro k
    fin_cases k
    · rfl
    · exact A'.map_id i
    · exact A.map_id i
    · rfl)
  map_comp a b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext _ _ (by
    intro k
    fin_cases k
    · exact (Category.id_comp _).symm
    · exact A'.map_comp a b
    · exact A.map_comp a b
    · exact (Category.id_comp _).symm)

lemma upperOriginalDiagram_insert :
    upperOriginalDiagram W A' A p' hp' α σ hA' hA ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.upperInsert =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperDiagram W A' A p' hp' α σ hA' hA := by
  have ho (i : I) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.upperInsert
      (upperOriginal W (p'.app i) (hp' i) (α.app i) (σ.app i)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeObjects.upper W (p'.app i) (hp' i) (α.app i) (σ.app i) := by
    rw [← upperOriginal_append]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.upperInsert_obj W _ _ _ _
  apply CategoryTheory.Functor.hext ho
  intro i j a
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho i) (ho j)
  intro k
  change HEq (((upperOriginalDiagram W A' A p' hp' α σ hA' hA).map a).app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.upperInsert.cut k)) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.upperInsert_cut]
  fin_cases k <;> rfl

lemma upperOriginalDiagram_collapse :
    upperOriginalDiagram W A' A p' hp' α σ hA' hA ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postCollapse = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A' p' hp' (α ≫ σ) hA' := by
  have ho (i : I) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postCollapse
      (upperOriginal W (p'.app i) (hp' i) (α.app i) (σ.app i)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W (p'.app i) (hp' i) (α.app i ≫ σ.app i) := by
    rw [← upperOriginal_append]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postCollapse_obj W _ _ _ _
  apply CategoryTheory.Functor.hext ho
  intro i j a
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho i) (ho j)
  intro k
  change HEq (((upperOriginalDiagram W A' A p' hp' α σ hA' hA).map a).app
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postCollapse.cut k)) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postCollapse_cut]
  fin_cases k <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
