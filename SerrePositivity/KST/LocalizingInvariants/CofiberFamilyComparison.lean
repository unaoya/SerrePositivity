module

public import SerrePositivity.KST.LocalizingInvariants.CofiberAdjunctionCounit
public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence

/-!
概要：任意の矢印族の cofiber 選択を、普遍 cofiber 関手との合成と比較する。
方針：底辺評価の trivial Kan fibration 性を全関手圏に移し、同じ底辺の二つの族を比較。
規約：頂点ごとの同型ではなく全関手の同型。使われ方：元の差の関手への随伴の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)

/-- 同じ底辺を持つ二つの普遍四角形の全族は関手として同型。 -/
def diagramComparison : FunctorIso (CofiberDiagrams.lift X a)
    (a ≫ CofiberRotation.bottomSection X) := by
  apply ((isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X)).postcompose A
    ).isFullyFaithful.preimageVertexIso
  change FunctorIso (CofiberDiagrams.lift X a ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X)
    ((a ≫ CofiberRotation.bottomSection X) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X)
  rw [CofiberDiagrams.lift_bottom, Category.assoc,
    CofiberRotation.bottomSection_bottom, Category.comp_id]

/-- 元の選択された cofiber 関手の、矢印族に関する関手全体の比較。 -/
def compositionIso : FunctorIso (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X a) (a ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X (𝟙 _)) := by
  have h := FunctorIso.postcomp (FunctorIso.postcomp (diagramComparison X a)
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X)) (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  rw [CofiberDiagrams.lift_right_target] at h
  change FunctorIso (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X a)
    (((a ≫ CofiberDiagrams.lift X (𝟙 _)) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X) ≫ _) at h
  simpa only [Category.assoc, ← CofiberDiagrams.lift_right_target] using h

end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
