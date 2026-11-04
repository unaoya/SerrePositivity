module
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberZeroTargetComparison

public import SerrePositivity.KST.LocalizingInvariants.SuspensionExactFunctor
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyComparison

/-!
概要：零終点矢印族の cofiber は、元の始点の suspension と全関手として同型。
方針：零終点矢印の始点評価の同値で同じ切断と比較し、cofiber 関手で写す。
規約：対象ごとの同型に弱めない。使われ方：差の C 側を shift に同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
  (ha : ∀ x, IsZeroTargetArrow (a.app (Opposite.op ⦋0⦌) x))

def zeroTargetArrowComparison : FunctorIso a
    ((a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      SuspensionExact.arrow X) := by
  let a₀ : A ⟶ zeroTargetArrows X := fullSubcomplexLift IsZeroTargetArrow a ha
  have h : FunctorIso a₀
      ((a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        SuspensionExact.arrowSection X) := by
    apply ((isQCatEquivalence_of_trivialKanFibration (zeroTargetArrowSource X)).postcompose A
      ).isFullyFaithful.preimageVertexIso
    change FunctorIso (a₀ ≫ zeroTargetArrowSource X)
      (((a ≫ evaluateFunctorAt _) ≫ SuspensionExact.arrowSection X) ≫ zeroTargetArrowSource X)
    rw [Category.assoc, SuspensionExact.arrowSection_source, Category.comp_id]
    exact eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f)) (by
      rw [zeroTargetArrowSource, ← Category.assoc, fullSubcomplexLift_ι]))
  have hi := FunctorIso.postcomp h (fullSubcomplexOnVertices _ IsZeroTargetArrow).ι
  simpa only [SuspensionExact.arrow, Category.assoc, a₀, fullSubcomplexLift_ι] using hi

def cofiberZeroTargetIso : FunctorIso (CofiberFamily.cofiber X a)
    ((a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      SuspensionExact.map X) := by
  have h := FunctorIso.postcomp (zeroTargetArrowComparison X a ha)
    (CofiberFamily.cofiber X (𝟙 _))
  exact CofiberFamily.compositionIso X a ≪≫ (by
    simpa only [SuspensionExact.map, Category.assoc] using h)

end SerrePositivity.KST.LocalizingInvariants
