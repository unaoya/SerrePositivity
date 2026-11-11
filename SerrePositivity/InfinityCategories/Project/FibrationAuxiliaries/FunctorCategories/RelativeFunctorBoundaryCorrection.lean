module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorEssentialExtension
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorRestrictionFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：相対射の境界条件を同型による一致から厳密な一致へ直す。
方針：単射による制限の left fibration 性で境界の辺を持ち上げる。
規約：全空間の相対射の同型を保持する。
使われ方：写像円柱から collage へ戻した pointed な図式の指定両端を固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 概要：Kan な始域の left fibration は像の頂点との同型を厳密な逆像へ移す。
方針：同型の代表辺を始点から持ち上げ終点を取る。
規約：持ち上げの始点と終点は始域内でも同型。
使われ方：相対関手空間の境界制限の厳密化。 -/
lemma leftFibration_exists_vertex_lift_of_iso {X Y : SSet.{u}}
    [KanComplex X] [Quasicategory Y] (p : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (x : X _⦋0⦌) (y : Y _⦋0⦌) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (p.app _ x) y) :
    ∃ z : X _⦋0⦌, p.app _ z = y ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x z) := by
  obtain ⟨β, hβ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (p.app _ x) y e.hom
  obtain ⟨F, hF₀, hFp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftEdge_source p x β
  let s := SSet.yonedaEquiv F
  let z := X.δ 0 s
  have hs : X.δ 1 s = x := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₀, Equiv.apply_symm_apply]
  have hz : p.app _ z = y := by
    change p.app _ (X.δ 0 s) = y
    change p.app _ (X.map (SimplexCategory.δ 0).op s) = y
    rw [CategoryTheory.NatTrans.naturality_apply]
    change Y.δ 0 ((p.app _ ) s) = y
    rw [← SSet.yonedaEquiv_comp, hFp]
    exact (congrArg (fun s : Y _⦋1⦌ ↦ Y.δ 0 s)
      ((SSet.yonedaEquiv (X := Y) (n := ⦋1⦌)).apply_symm_apply β.edge)).trans β.tgt_eq
  let γ : SSet.Truncated.Edge (X := (truncation 2).obj X) x z := ⟨s, hs, rfl⟩
  have : IsGroupoid (hoFunctor.obj X) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.kanComplex_ho_isGroupoid X
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk γ) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj X) _
  exact ⟨z, hz, ⟨asIso (SSet.Truncated.HomotopyCategory.homMk γ)⟩⟩

/-- 概要：単射上の指定した相対射と同型な制限を厳密な一致に直せる。
方針：相対関手空間の left fibration に境界の同型の持ち上げを適用する。
規約：元の全体の相対射との同型も保持する。
使われ方：coherent な変換から得た collage の両端の厳密化。 -/
lemma exists_relativeFunctor_boundary_correction {A D E B : SSet.{u}}
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : A ⟶ B) (i : D ⟶ A) [Mono i]
    (L : A ⟶ E) (hL : L ≫ p = b) (W : D ⟶ E) (hW : W ≫ p = i ≫ b)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ b) (i ≫ L) (by rw [Category.assoc, hL]))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ b) W hW)) :
    ∃ (L' : A ⟶ E) (hL' : L' ≫ p = b), i ≫ L' = W ∧
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p b L hL) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p b L' hL')) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p b i).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p b L hL))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ b) W hW) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPre_vertex]
    exact e
  obtain ⟨z, hz, h⟩ := leftFibration_exists_vertex_lift_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre p b i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p b L hL) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex p (i ≫ b) W hW) he
  obtain ⟨L', hL', hLz⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_relativeFunctorVertex p b z
  rw [← hLz, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPre_vertex] at hz
  refine ⟨L', hL', ?_, ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective (congrArg Subtype.val hz)
  · rwa [← hLz] at h

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
