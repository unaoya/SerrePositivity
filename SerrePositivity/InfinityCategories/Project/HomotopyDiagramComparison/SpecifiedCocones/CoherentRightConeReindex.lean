module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoherentRightConeFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomNaturality

/-!
# 元の coherent 錐の全 Hom の添字変換

概要：通常前面の引き戻しと最後 Hom の自然性から全 Hom の自然性を得る。
方針：最後の頂点を固定した延長と元の Hom の端点正規化を使う。
規約：全ての面・退化と元の全 path を保持する。
使われ方：native roof の混合単体を全 slice prism へ束ねる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open CategoryTheory SimplicialThickening SSet MonoidalCategory CartesianMonoidalCategory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {m n : ℕ}
  (F : Fin (n + 1) ⥤ C) (Y : C)

omit [SimplicialCategory C] in
lemma obj_extend (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 2)) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom i) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj (α.toOrderHom.monotone.functor ⋙ F) Y i := by
  induction i using Fin.lastCases
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_last, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_last]
  · rename_i i
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_cast, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_cast]
    rfl

variable (L : ∀ i : Fin (n + 1),
  SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex.{u} i.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex (Fin.last (n + 1))) ⟶
    SimplicialCategory.sHom (F.obj i) Y)

lemma hom_transport {i j i' j' : Fin (n + 2)} (hi : i = i') (hj : j = j')
    {A B : C} (hA : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y i' = A) (hB : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y j' = B) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom F Y L i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y) hi).trans hA) ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y) hj).trans hB)) =
    eqToHom (congrArg₂ (fun a b : Fin (n + 2) =>
      SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex.{u} a) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex b)) hi hj) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom F Y L i' j' ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) := by
  subst i'
  subst j'
  simp only [eqToHom_refl, Category.id_comp]

lemma frontHom_reindex (α : ⦋m⦌ ⟶ ⦋n⦌) (i j : Fin (m + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtendHom.{u} α i.castSucc j.castSucc ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) =>
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex.{u} a) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex b))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α.toOrderHom i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α.toOrderHom j))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.frontHom F (α.toOrderHom i) (α.toOrderHom j) =
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.frontHom (α.toOrderHom.monotone.functor ⋙ F) i j := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

variable (α : ⦋m⦌ ⟶ ⦋n⦌)
  (M : ∀ i : Fin (m + 1),
    SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex.{u} i.castSucc) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.vertex (Fin.last (m + 1))) ⟶
      SimplicialCategory.sHom (F.obj (α.toOrderHom i)) Y)

lemma hom_reindex_of_normalized (i j : Fin (m + 2)) {A B : C}
    (hA : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj (α.toOrderHom.monotone.functor ⋙ F) Y i = A)
    (hB : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj (α.toOrderHom.monotone.functor ⋙ F) Y j = B)
    (hA' : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom i) = A)
    (hB' : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom j) = B)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtendHom.{u} α i j ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom F Y L
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom i) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom j) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom hA' hB') =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom (α.toOrderHom.monotone.functor ⋙ F) Y M i j ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom hA hB)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtendHom.{u} α i j ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom F Y L
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom i) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom j)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom (obj_extend F Y α i) (obj_extend F Y α j)) =
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom (α.toOrderHom.monotone.functor ⋙ F) Y M i j := by
  apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom hA hB))).1
  simpa only [Category.assoc, eqToHom_trans] using h

variable (hM : ∀ i, nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastReindexFunctor.{u} α i) ≫ L (α.toOrderHom i) = M i)

include hM in
lemma hom_reindex (i j : Fin (m + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtendHom.{u} α i j ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom F Y L
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom i) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom α.toOrderHom j)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom (obj_extend F Y α i) (obj_extend F Y α j)) =
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom (α.toOrderHom.monotone.functor ⋙ F) Y M i j := by
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    let hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α.toOrderHom
    let hN := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_last F Y
    let hM := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_last (α.toOrderHom.monotone.functor ⋙ F) Y
    apply hom_reindex_of_normalized F Y L α M _ _ hM hM
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y) hi).trans hN) ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y) hi).trans hN)
    rw [hom_transport F Y L hi hi hN hN]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom_last_last, comp_toUnit_assoc]
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change m + 1 ≤ j.val at h
    omega
  case cast.last i =>
    let hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α.toOrderHom i
    let hj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last α.toOrderHom
    let hNi := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_cast F Y (α.toOrderHom i)
    let hNj := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_last F Y
    let hMi := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_cast (α.toOrderHom.monotone.functor ⋙ F) Y i
    let hMj := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_last (α.toOrderHom.monotone.functor ⋙ F) Y
    apply hom_reindex_of_normalized F Y L α M _ _ hMi hMj
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y) hi).trans hNi) ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y) hj).trans hNj)
    rw [hom_transport F Y L hi hj hNi hNj]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom_cast_last]
    rw [← Category.assoc]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtendHom]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.thickeningExtend_map_cast_last]
    exact hM i
  case cast.cast i j =>
    let hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α.toOrderHom i
    let hj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc α.toOrderHom j
    let hNi := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_cast F Y (α.toOrderHom i)
    let hNj := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_cast F Y (α.toOrderHom j)
    let hMi := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_cast (α.toOrderHom.monotone.functor ⋙ F) Y i
    let hMj := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj_cast (α.toOrderHom.monotone.functor ⋙ F) Y j
    apply hom_reindex_of_normalized F Y L α M _ _ hMi hMj
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y) hi).trans hNi) ((congrArg (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.obj F Y) hj).trans hNj)
    rw [hom_transport F Y L hi hj hNi hNj]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentRightConeHom.hom_cast_cast]
    exact frontHom_reindex F α i j

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
