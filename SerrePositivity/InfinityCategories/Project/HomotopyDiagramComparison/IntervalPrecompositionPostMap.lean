module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalComposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostIso

/-!
概要：元の区間 Hom 前合成は、単体的関手の元の Hom 作用と全パラメータで両立する。
方針：元の h Fun の作用と定値関手の輸送の可換式を使う。
規約：端点を正規化しても元の前合成と指定辺の一単体を保持する。
使われ方：Yoneda 評価の自然性を P_Σ の元の包含作用へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の前合成と単体的関手の元の区間 Hom 作用は、一つの関手同型で可換。 -/
def intervalFunctorMap_precomposeIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y)
    {a b : X _⦋0⦌} (e : SSet.Edge a b) (z : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose z (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap p a z)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap p b z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose (p.app (Opposite.op ⦋0⦌) z)
        (SSet.Truncated.HomotopyCategory.homMk (e.map p).toTruncated)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy
  apply Classical.choice
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom_eq_imp_homotopy
  let K := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace b z
  let γ := SSet.Truncated.HomotopyCategory.homMk e.toTruncated
  have hconst := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_postcomp K p γ
  have hc := congrArg (fun t ↦ t ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K b p).inv) hconst
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at hc
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorMap_familyHom, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_hom, Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_family]
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalFunctorMap_familyHom (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace b z)) p
  simp only [Category.id_comp] at hm
  rw [hm]
  have h := congrArg (fun t ↦ t ≫
    (hoFunctor.map ((ihom K).map p)).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (𝟙 K)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.constantFunctorCompIso K z p).hom) hc
  simp only [Category.assoc] at h ⊢
  exact h

/-- 端点の表示を変えない正規化 Hom 作用は、元の区間関手作用と厳密に一致する。 -/
lemma intervalMappingPostOfEq_refl_eq_functorMap {X Y : SSet.{u}} (p : X ⟶ Y)
    (a b : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq p a b rfl rfl = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap p a b := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq_uncurry p a b rfl rfl (𝟙 _)
  have h' := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap_uncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace a b)) p
  simp only [Category.id_comp] at h h'
  exact h.trans h'.symm

/-- 端点表示を正規化しても、元の前合成と同じ指定辺の Hom 作用は全族で可換。 -/
def intervalMappingPostOfEq_precomposeIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y)
    {a b : X _⦋0⦌} (e : SSet.Edge a b) (z : X _⦋0⦌) {a' b' z' : Y _⦋0⦌}
    (ha : p.app (Opposite.op ⦋0⦌) a = a') (hb : p.app (Opposite.op ⦋0⦌) b = b')
    (hz : p.app (Opposite.op ⦋0⦌) z = z') (e' : SSet.Edge a' b')
    (he : p.app (Opposite.op ⦋1⦌) e.edge = e'.edge) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose z (SSet.Truncated.HomotopyCategory.homMk e.toTruncated) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq p a z ha hz)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq p b z hb hz ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose z' (SSet.Truncated.HomotopyCategory.homMk e'.toTruncated)) := by
  subst a' b' z'
  have he' : e.map p = e' := SSet.Edge.ext he
  subst e'
  rw [intervalMappingPostOfEq_refl_eq_functorMap, intervalMappingPostOfEq_refl_eq_functorMap]
  exact intervalFunctorMap_precomposeIso p e z

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
