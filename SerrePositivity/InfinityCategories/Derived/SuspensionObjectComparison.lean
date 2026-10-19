module
public import SerrePositivity.InfinityCategories.Derived.StandardSuspensionSquare

/-! # Suspension と複体シフトの対象上の比較

概要：実際の標準 suspension 四角形を使って、D3 による suspension の像を一回シフトと比較する。
方針：suspension の選択の比較、標準 cone 接続同型、局所化のシフト比較を合成する。
規約：自然性は後続で証明する。使われ方：D7 の CommShift の成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (S : Type u) [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 通常の h D(S) からの D3 比較と元の複体の導来像の標準同型。 -/
def derivedStableHomotopyEquivalenceVertexIso (X : Semifree S) :
    (derivedStableHomotopyEquivalence S).functor.obj
      (SSet.HomotopyCategory.mk (Simplex.vertex X)) ≅ DerivedCategory.Q.obj X.val :=
  (DerivedCategory.quotientCompQhIso (ModuleCat S)).app X.val

/-- 実際の suspension の導来像と複体の一回シフトの比較同型。 -/
def derivedSuspensionObjectIso (X : Semifree S) :
    (derivedStableHomotopyEquivalence S).functor.obj
      ((suspensionFunctor (derivedInfinityCategory S)).obj
        (SSet.HomotopyCategory.mk (Simplex.vertex X))) ≅
      (DerivedCategory.Q.obj X.val)⟦(1 : ℤ)⟧ := by
  refine (derivedStableHomotopyEquivalence S).functor.mapIso
      (semifreeSuspensionSquare X).suspensionFunctorObjIso ≪≫
    eqToIso (congrArg (fun x => (derivedStableHomotopyEquivalence S).functor.obj
      (SSet.HomotopyCategory.mk x)) (semifreeSuspensionSquare_vertex X)) ≪≫ ?_
  exact derivedStableHomotopyEquivalenceVertexIso S (semifreeSuspensionObject X) ≪≫
    DerivedCategory.Q.mapIso (semifreeSuspensionComplexIso X) ≪≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val

end SerrePositivity.InfinityCategories
