module

public import SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.CofiberExactPostcomposition
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyComparison

/-!
概要：完全関手と選んだ cofiber 関手の間に、全関手圏内の自然比較同型を構成する。
方針：完全関手で写した cofiber 図式と同じ底辺の選択を、自明 Kan fibration 上で比較する。
規約：点ごとの同型の族に弱めない。使われ方：cofiber 関手による元の分母の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
variable {X Y : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
  [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y] (F : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F]

def exactDiagramComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (CofiberDiagrams.lift X (𝟙 _) ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp F)
    ((ihom (Δ[1] : SSet.{u})).map F ≫ CofiberDiagrams.lift Y (𝟙 _)) := by
  apply ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom Y)).postcompose
    ((ihom (Δ[1] : SSet.{u})).obj X)).isFullyFaithful.preimageVertexIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((CofiberDiagrams.lift X (𝟙 _) ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp F) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom Y)
    (((ihom (Δ[1] : SSet.{u})).map F ≫ CofiberDiagrams.lift Y (𝟙 _)) ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.bottom Y)
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_bottom, ← Category.assoc,
    CofiberDiagrams.lift_bottom, Category.id_comp, Category.assoc,
    CofiberDiagrams.lift_bottom, Category.comp_id]

def exactNaturality : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X (𝟙 _) ≫ F)
    ((ihom (Δ[1] : SSet.{u})).map F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Y (𝟙 _)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (exactDiagramComparison F)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  have hl : (CofiberDiagrams.lift X (𝟙 _) ≫ _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp F) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X (𝟙 _) ≫ F := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StablePresentableInfinityCategories.Exact.postcomp_cofiber, ← Category.assoc,
      ← Category.assoc, CofiberDiagrams.lift_right_target]
  have hr : ((ihom (Δ[1] : SSet.{u})).map F ≫ CofiberDiagrams.lift Y (𝟙 _)) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberDiagrams.right Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
        (ihom (Δ[1] : SSet.{u})).map F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Y (𝟙 _) := by
    rw [Category.assoc, ← Category.assoc (CofiberDiagrams.lift Y (𝟙 _)),
      CofiberDiagrams.lift_right_target]
  rw [hl, hr] at h
  exact h

end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
