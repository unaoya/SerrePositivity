module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.StandardSuspensionSquare

/-! # Suspension と複体シフトの対象上の比較

概要：実際の標準 suspension 四角形を使って、D3 による suspension の像を一回シフトと比較する。
方針：suspension の選択の比較、標準 cone 接続同型、局所化のシフト比較を合成する。
規約：自然性は後続で証明する。使われ方：D7 の CommShift の成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 通常の h D(S) からの D3 比較と元の複体の導来像の標準同型。 -/
def derivedStableHomotopyEquivalenceVertexIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.obj
      (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X)) ≅ DerivedCategory.Q.obj X.val :=
  (DerivedCategory.quotientCompQhIso (ModuleCat S)).app X.val

/-- 実際の suspension の導来像と複体の一回シフトの比較同型。 -/
def derivedSuspensionObjectIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.obj
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.suspensionFunctor (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).obj
        (SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X))) ≅
      (DerivedCategory.Q.obj X.val)⟦(1 : ℤ)⟧ := by
  refine (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.mapIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare X).suspensionFunctorObjIso ≪≫
    eqToIso (congrArg (fun x => (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedStableHomotopyEquivalence S).functor.obj
      (SSet.HomotopyCategory.mk x)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionSquare_vertex X)) ≪≫ ?_
  exact derivedStableHomotopyEquivalenceVertexIso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionObject X) ≪≫
    DerivedCategory.Q.mapIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeSuspensionComplexIso X) ≪≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val

end SerrePositivity.InfinityCategories.Project.DerivedCategories
