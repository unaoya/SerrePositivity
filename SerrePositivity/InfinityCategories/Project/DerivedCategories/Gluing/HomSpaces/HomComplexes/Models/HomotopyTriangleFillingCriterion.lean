module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomComplexes.Models.HomotopyTriangleBoundary
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle

/-! # 指定した全区間三辺の境界充填判定

概要：関手圏の合成等式と、指定した三辺そのものを保つ境界充填を同定する。
方針：実合成三角形と境界の面ごとの外延性を使う。
規約：辺の代表を取り替えず、パラメーター単体集合を任意とする。
使われ方：入力固定変形の類の比較を正本の指定境界充填へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {a b c : K ⟶ X}
  {l : SSet.Homotopy a b} {r : SSet.Homotopy b c} {d : SSet.Homotopy a c}

lemma dgGluingFunctorCompositionTriangle_boundary (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d) :
    (boundary 2).ι ≫ T.diagram = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary l r d := by
  apply boundary.hom_ext
  intro i
  fin_cases i <;> dsimp
  · rw [← Category.assoc, boundary.ι_ι, T.face_zero,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary_zero]
  · rw [← Category.assoc, boundary.ι_ι, T.face_one,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary_one]
  · rw [← Category.assoc, boundary.ι_ι, T.face_two,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary_two]

lemma dgGluingHomotopyTriangleFilling_of_homEq [Quasicategory X]
    (h : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d)) :
    ∃ T : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj X,
      (boundary 2).ι ≫ T = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary l r d := by
  obtain ⟨T⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.nonempty_functorCompositionTriangle_of_homEq l r d h
  exact ⟨T.diagram, dgGluingFunctorCompositionTriangle_boundary T⟩

lemma dgGluingFunctorCompositionTriangle_homEq (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d) :
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d) := by
  apply SSet.Truncated.HomotopyCategory.homMk_comp_homMk
  refine ⟨SSet.yonedaEquiv T.diagram, ?_, ?_, ?_⟩
  · exact (stdSimplex.yonedaEquiv_δ_comp T.diagram 2).symm.trans
      (congrArg SSet.yonedaEquiv T.face_two)
  · exact (stdSimplex.yonedaEquiv_δ_comp T.diagram 0).symm.trans
      (congrArg SSet.yonedaEquiv T.face_zero)
  · exact (stdSimplex.yonedaEquiv_δ_comp T.diagram 1).symm.trans
      (congrArg SSet.yonedaEquiv T.face_one)

lemma dgGluingHomotopyTriangleFilling_iff [Quasicategory X] :
    (∃ T : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj X,
      (boundary 2).ι ≫ T = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary l r d) ↔
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) =
        SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d) := by
  constructor
  · rintro ⟨T, hT⟩
    apply dgGluingFunctorCompositionTriangle_homEq (l := l) (r := r) (d := d)
    refine ⟨T, ?_, ?_, ?_⟩
    · have h := congrArg (fun q => boundary.ι (0 : Fin 3) ≫ q) hT
      simpa only [← Category.assoc, boundary.ι_ι,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary_zero] using h
    · have h := congrArg (fun q => boundary.ι (1 : Fin 3) ≫ q) hT
      simpa only [← Category.assoc, boundary.ι_ι,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary_one] using h
    · have h := congrArg (fun q => boundary.ι (2 : Fin 3) ≫ q) hT
      simpa only [← Category.assoc, boundary.ι_ι,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary_two] using h
  · exact dgGluingHomotopyTriangleFilling_of_homEq

lemma dgGluingHomotopyTriangleFilling_transfer [Quasicategory X]
    {l' : SSet.Homotopy a b} {r' : SSet.Homotopy b c} {d' : SSet.Homotopy a c}
    (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d)
    (hl : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy l'))
    (hr : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r'))
    (hd : SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d) =
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy d')) :
    ∃ V : (Δ[2] : SSet.{u}) ⟶ (ihom K).obj X,
      (boundary 2).ι ≫ V = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingHomotopyTriangleBoundary l' r' d' := by
  apply dgGluingHomotopyTriangleFilling_of_homEq
  rw [← hl, ← hr, ← hd]
  exact dgGluingFunctorCompositionTriangle_homEq T

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
