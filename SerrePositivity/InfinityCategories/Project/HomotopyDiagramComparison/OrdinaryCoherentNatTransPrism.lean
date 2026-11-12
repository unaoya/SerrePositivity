module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OrdinaryNatTransPrism
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentUnderlyingHo
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.ThinNerveInnerFibration

/-!
概要：元の通常の自然変換の prism を、成分を変更せず coherent nerve へ写す。
方針：元の通常の比較の prism と、同じ終点の Cartesian 輸送の一意性を使う。
規約：全対象・全射の作用を指定された関手のまま比較する。使われ方：HTT 5.2.4.6。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

variable {C D : Type v} [Category.{u} C] [Category.{u} D] [SimplicialCategory D]

/-- 元の通常の自然変換の区間族を、同じ coherent 表示へ写す。 -/
def ordinaryCoherentNatTransPrism {F G : C ⥤ D} (η : F ⟶ G) :
    (Δ[1] : SSet.{max u v}) ⊗ nerve C ⟶ SimplicialNerve D :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ordinaryNatTransPrism η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent D

/-- 元の始域関手の通常の nerve の coherent 表示は、区間族の始点である。 -/
lemma ordinaryCoherentNatTransPrism_zero {F G : C ⥤ D} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (nerve C) ≫ ordinaryCoherentNatTransPrism η =
      nerveMap F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent D := by
  rw [ordinaryCoherentNatTransPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ordinaryNatTransPrism_zero]

/-- 元の終域関手の通常の nerve の coherent 表示は、区間族の終点である。 -/
lemma ordinaryCoherentNatTransPrism_one {F G : C ⥤ D} (η : F ⟶ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (nerve C) ≫ ordinaryCoherentNatTransPrism η =
      nerveMap G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent D := by
  rw [ordinaryCoherentNatTransPrism, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ordinaryNatTransPrism_one]

/-- 元の各指定成分の通常射の coherent 辺は、区間族の同じ頂点の辺に一致する。 -/
lemma ordinaryCoherentNatTransPrism_vertexEdge {F G : C ⥤ D} (η : F ⟶ G) (x : C) :
    (ordinaryCoherentNatTransPrism η).app (Opposite.op ⦋1⦌)
      (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{max u v})),
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x) 1) = (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (η.app x)).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.nerveToCoherent D).app (Opposite.op ⦋1⦌)
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ordinaryNatTransPrism η).app (Opposite.op ⦋1⦌) _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ordinaryNatTransPrism_vertexEdge]
  rfl

/-- 区間への射の両端が零と一なら、元の prism の全次数の底は時刻の射影に一致する。 -/
lemma prism_projection_of_endpoints {A E : SSet.{u}}
    (p : E ⟶ (Δ[1] : SSet.{u})) (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ E)
    (h0 : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H) ≫ p =
      SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
    (h1 : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H) ≫ p =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
    H ≫ p = CategoryTheory.CartesianMonoidalCategory.fst (Δ[1] : SSet.{u}) A := by
  apply (cancel_mono (stdSimplex.isoNerve 1).hom).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  rintro ⟨t, x⟩
  obtain ⟨j, rfl⟩ := (stdSimplex.obj₀Equiv (n := 1)).symm.surjective t
  fin_cases j
  · have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) h0
    change p.app (Opposite.op ⦋0⦌)
      (H.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) 0, x)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) 0 at h
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at h
    exact congrArg (fun y ↦ (stdSimplex.isoNerve 1).hom.app (Opposite.op ⦋0⦌) y) h
  · have h := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) x) h1
    change p.app (Opposite.op ⦋0⦌)
      (H.app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) 0, x)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) 0 at h
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at h
    exact congrArg (fun y ↦ (stdSimplex.isoNerve 1).hom.app (Opposite.op ⦋0⦌) y) h

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
