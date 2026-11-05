module

public import SerrePositivity.KST.LocalizingInvariants.CofiberRotationAdjunction
public import SerrePositivity.KST.LocalizingInvariants.CofiberRelativeRightComparison
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyPrecomposition
public import SerrePositivity.InfinityCategories.Stable.EquivalenceStability

/-!
概要：逆 cofiber 回転は完全で、その cofiber は元の矢印の終点と関手として同型。
方針：右辺の厳密切断の普遍四角形を同じ底辺の選択と比較する。
規約：安定性は入力圏だけに要求。使われ方：一般商から恒等 lax 差への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberRotation
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]

instance rightSection_isExact : IsExactFunctor (rightSection X) := by
  have he : IsExactFunctor (rightSection X ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X) := by
    rw [rightSection_right]
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Stable.Exact.exact_of_postcomp_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X) (rightSection X)

instance inverseRotation_isExact : IsExactFunctor (inverseRotation X) := by
  have hb : IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X) :=
    isExactFunctor_of_isQCatEquivalence
      (isQCatEquivalence_of_trivialKanFibration (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X))
  change IsExactFunctor (rightSection X ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottom X)
  infer_instance

lemma inverseRotation_target : inverseRotation X ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [inverseRotation, Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.bottomTarget_eq_rightSource,
    ← Category.assoc, rightSection_right, Category.id_comp]

def inverseRotationDiagramComparison : FunctorIso (rightSection X)
    (CofiberDiagrams.lift X (inverseRotation X)) :=
  CofiberDiagrams.relativeComparison X _ _ (by rw [CofiberDiagrams.lift_bottom]; rfl)

def inverseRotationCofiberIso : FunctorIso (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X (inverseRotation X))
    (evaluateFunctorAt (Y := X) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  have e := FunctorIso.postcomp (inverseRotationDiagramComparison X)
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams.right X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  rw [← Category.assoc, rightSection_right, Category.id_comp,
    ← Category.assoc, CofiberDiagrams.lift_right_target] at e
  exact e.symm

def inverseRotationFamilyCofiberIso {A : SSet.{u}}
    (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    FunctorIso (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X (a ≫ inverseRotation X))
      (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :=
  (CofiberFamily.precompositionIso (inverseRotation X) a).symm ≪≫
    FunctorIso.precomp (inverseRotationCofiberIso X) a

end SerrePositivity.KST.LocalizingInvariants.CofiberRotation
