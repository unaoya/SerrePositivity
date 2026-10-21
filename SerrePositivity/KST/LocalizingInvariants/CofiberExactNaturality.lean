module

public import SerrePositivity.KST.LocalizingInvariants.CofiberExactPostcomposition
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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
variable {X Y : SSet.{u}} [Quasicategory X] [IsStable X]
  [Quasicategory Y] [IsStable Y] (F : X ⟶ Y) [IsExactFunctor F]

def exactDiagramComparison : FunctorIso
    (CofiberDiagrams.lift X (𝟙 _) ≫ CofiberDiagrams.postcomp F)
    ((ihom (Δ[1] : SSet.{u})).map F ≫ CofiberDiagrams.lift Y (𝟙 _)) := by
  apply ((isQCatEquivalence_of_trivialKanFibration (CofiberDiagrams.bottom Y)).postcompose
    ((ihom (Δ[1] : SSet.{u})).obj X)).isFullyFaithful.preimageVertexIso
  change FunctorIso
    ((CofiberDiagrams.lift X (𝟙 _) ≫ CofiberDiagrams.postcomp F) ≫ CofiberDiagrams.bottom Y)
    (((ihom (Δ[1] : SSet.{u})).map F ≫ CofiberDiagrams.lift Y (𝟙 _)) ≫
      CofiberDiagrams.bottom Y)
  rw [Category.assoc, CofiberDiagrams.postcomp_bottom, ← Category.assoc,
    CofiberDiagrams.lift_bottom, Category.id_comp, Category.assoc,
    CofiberDiagrams.lift_bottom, Category.comp_id]

def exactNaturality : FunctorIso (cofiber X (𝟙 _) ≫ F)
    ((ihom (Δ[1] : SSet.{u})).map F ≫ cofiber Y (𝟙 _)) := by
  have h := FunctorIso.postcomp (exactDiagramComparison F)
    (CofiberDiagrams.right Y ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  have hl : (CofiberDiagrams.lift X (𝟙 _) ≫ CofiberDiagrams.postcomp F) ≫
      (CofiberDiagrams.right Y ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
        cofiber X (𝟙 _) ≫ F := by
    rw [Category.assoc, CofiberDiagrams.postcomp_cofiber, ← Category.assoc,
      ← Category.assoc, CofiberDiagrams.lift_right_target]
  have hr : ((ihom (Δ[1] : SSet.{u})).map F ≫ CofiberDiagrams.lift Y (𝟙 _)) ≫
      (CofiberDiagrams.right Y ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
        (ihom (Δ[1] : SSet.{u})).map F ≫ cofiber Y (𝟙 _) := by
    rw [Category.assoc, ← Category.assoc (CofiberDiagrams.lift Y (𝟙 _)),
      CofiberDiagrams.lift_right_target]
  rw [hl, hr] at h
  exact h

end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
