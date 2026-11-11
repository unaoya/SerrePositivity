module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SkeletalLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FinalHornProductBoundary

/-! # 最後の頂点による外側ホーンの相対充填

概要：指定部分外の各単体の終点上の辺が可逆なら、最後の外側ホーンの族を延長できる。
方針：相対骨格の各セルで最後の外側ホーンと境界の積の充填を使う。
規約：パラメーターの quasicategory 性は不要。使われ方：余錐の cartesian 性。

対応節は Kerodon 5.3（Tag 035A）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
  SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：指定部分外の単体の最後の頂点でホーンの最後の辺が可逆なら図式を相対的に延長できる。
方針：各相対セルの境界上の族とホーン上の指定図式を積の pushout で貼り、可逆な辺による積の充填を使う。
規約：X は quasicategory、i は任意の単射、パラメーターに追加の仮定はない。
使われ方：Kerodon §5.3.7（Tag 01US） の錐の制限の終端の外側ホーンの充填。 -/
lemma finalHornRestriction_lift_of_last_vertices {A D X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ D) [Mono i] (m : ℕ)
    (a : A ⟶ (ihom (Δ[m + 2] : SSet.{u})).obj X)
    (b : D ⟶ (ihom (horn (m + 2) (Fin.last (m + 2)) : SSet.{u})).obj X)
    (hw : a ≫ (pre (horn (m + 2) (Fin.last (m + 2))).ι).app X = i ≫ b)
    (ht : ∀ (n : ℕ) (s : D _⦋n⦌), s ∉ Set.range (i.app (Opposite.op ⦋n⦌)) →
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((uncurry b).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex s) 1)))) :
    ∃ F : D ⟶ (ihom (Δ[m + 2] : SSet.{u})).obj X,
      i ≫ F = a ∧ F ≫ (pre (horn (m + 2) (Fin.last (m + 2))).ι).app X = b := by
  let p := (pre (horn (m + 2) (Fin.last (m + 2))).ι).app X
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_lift_of_skeletal_lifts i p a b hw
  intro d f hf hfp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_lift_skeletonOfMono_succ i p b d f hfp
  intro c
  let u := c.ιSigmaBoundary ≫ t i d ≫ f
  let G := uncurry u
  let H := uncurry (c.map ≫ b)
  have hu : u ≫ p = (boundary d).ι ≫ c.map ≫ b := by
    dsimp [u]
    rw [Category.assoc, Category.assoc, hfp]
    have hcι : c.ιSigmaBoundary ≫ t i d ≫ (skeletonOfMono i d).ι =
        (boundary d).ι ≫ c.map := by
      simp [Cell.ιSigmaBoundary, t]
    simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ b) hcι
  have hprod : ((horn (m + 2) (Fin.last (m + 2))).ι ▷ (boundary d : SSet.{u})) ≫ G =
      ((horn (m + 2) (Fin.last (m + 2)) : SSet.{u}) ◁ (boundary d).ι) ≫ H := by
    have hh := congrArg uncurry hu
    change uncurry (u ≫ (pre (horn (m + 2) (Fin.last (m + 2))).ι).app X) = _ at hh
    rw [uncurry_pre_app, uncurry_natural_left] at hh
    exact hh
  have hedge : H.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last d)) 1) =
      (uncurry b).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexLastVertex c.simplex) 1) := by
    dsimp [H]
    rw [uncurry_natural_left]
    change (uncurry b).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m, c.map.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last d)) 1)) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map]
    rfl
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge m, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (Fin.last d)) 1))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hedge).2 (ht d c.simplex c.notMem)
  obtain ⟨F, hF₁, hF₂⟩ := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.finalHornProduct_fill_boundary m d G H hprod hi
  refine ⟨curry F, ?_, ?_⟩
  · apply uncurry_injective
    rw [uncurry_natural_left, uncurry_curry]
    exact hF₁
  · apply uncurry_injective
    change uncurry (curry F ≫ (pre (horn (m + 2) (Fin.last (m + 2))).ι).app X) = _
    rw [uncurry_pre_app, uncurry_curry]
    exact hF₂


end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
