module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ReplacementInnerHorn
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FinalHornFamily

/-!
概要：有限鎖上の replacement の最後の外ホーン上の図式を可逆化条件から延長する。
方針：始対象の係数との積を外ホーンの族として充填し、replacement の pushout で貼る。
規約：可逆性を課すのは指定した終端辺の族である。
使われ方：相対指数の特殊な辺の cartesian 性の模型側の充填。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：最後の外ホーン上の図式を始対象係数のパラメータ付き図式へ戻す。
方針：標準単体と有限鎖の nerve の同型と、部分底の組み立て射を使う。
規約：図式 F の係数値の充填性は不要。
使われ方：延長に必要な終端辺の可逆性を具体的に記述する。 -/
def replacementFinalHornDiagram (n : ℕ)
    (F : ULift.{u} (Fin (n + 3)) ⥤ SSet.{u}) {D : SSet.{u}}
    (H : ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) : SSet.{u}) ⟶ D) :
    (horn (n + 2) (Fin.last (n + 2)) : SSet.{u}) ⊗ F.obj (ULift.up 0) ⟶ D :=
  ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso (horn (n + 2) (Fin.last (n + 2)))
    (stdSimplex.isoNerve (n + 2)).symm).inv ▷ F.obj (ULift.up 0)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementInitialSubcomplexMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 2))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))) ≫ H

/-- 概要：replacement の最後の外ホーン上の図式は指定終端辺の族が可逆なら延長できる。
方針：外ホーンと始対象係数の積の充填を、部分底と全体の pushout に沿って貼る。
規約：D は quasicategory、F は任意の単体集合値図式。
使われ方：cartesian ホーンの持ち上げを構成するための模型側の延長。 -/
lemma exists_kanReplacementFinalHorn_extension (n : ℕ)
    (F : ULift.{u} (Fin (n + 3)) ⥤ SSet.{u}) {D : SSet.{u}} [Quasicategory D]
    (H : ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) : SSet.{u}) ⟶ D)
    (he : ∀ x : (F.obj (ULift.up 0)) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((replacementFinalHornDiagram n F H).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)))) :
    ∃ G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ D,
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)).ι ≫ G = H := by
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn.{u} (n + 2) (Fin.last (n + 2))
  let K := F.obj (ULift.up 0)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.subcomplexPreimageIso (horn (n + 2) (Fin.last (n + 2)))
    (stdSimplex.isoNerve.{u} (n + 2)).symm
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementInitialSubcomplexMap F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 2)) A
  obtain ⟨L, hL⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_kanFinalHornFamily_extension n (replacementFinalHornDiagram n F H) he
  let L' := ((stdSimplex.isoNerve.{u} (n + 2)).inv ▷ K) ≫ L
  have hι : e.hom ≫ (horn (n + 2) (Fin.last (n + 2))).ι =
      A.ι ≫ (stdSimplex.isoNerve (n + 2)).inv := rfl
  have hL' : (A.ι ▷ K) ≫ L' = k ≫ H := by
    dsimp only [L']
    rw [← Category.assoc, ← comp_whiskerRight, ← hι, comp_whiskerRight, Category.assoc, hL]
    change (e.hom ▷ K) ≫ (e.inv ▷ K) ≫ k ≫ H = _
    rw [← Category.assoc, ← comp_whiskerRight, e.hom_inv_id, id_whiskerRight, Category.id_comp]
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementInitialSubcomplex_isPushout F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 2)) A
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn_contains_noninitial (n + 2) (Fin.last (n + 2)) (by
      change (0 : ℕ) < n + 2
      omega))
  exact ⟨q.desc H L' hL'.symm, q.inl_desc _ _ _⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
