module
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberZeroSourceComparison

public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyComparison

/-!
概要：零始点を持つ任意の矢印族の cofiber は、その終点の族と関手として同型。
方針：零始点矢印の終点評価の同値で右随伴の像と比較し、可逆余単位を使う。
規約：対象ごとの同型に弱めない。使われ方：差の関手と D 包含の合成の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
attribute [local instance] _root_.SerrePositivity.InfinityCategories.Stable.Exact.cofiberZeroComparisonQuasicategory
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
  (ha : ∀ x, IsZeroSourceArrow (a.app (Opposite.op ⦋0⦌) x))

/-- 元の零始点矢印族と、同じ終点を右随伴に入れた族の実関手同型。 -/
def zeroSourceArrowComparison :
    FunctorIso a ((a ≫ _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.target X) ≫ cofiberRightAdjoint X) := by
  let a₀ : A ⟶ zeroSourceArrows X := fullSubcomplexLift IsZeroSourceArrow a ha
  have h : FunctorIso a₀
      ((a ≫ _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.target X) ≫ cofiberRightAdjointZeroSource X) := by
    apply ((isQCatEquivalence_of_trivialKanFibration (zeroSourceArrowTarget X)).postcompose A
      ).isFullyFaithful.preimageVertexIso
    change FunctorIso (a₀ ≫ zeroSourceArrowTarget X)
      (((a ≫ _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.target X) ≫ cofiberRightAdjointZeroSource X) ≫
        zeroSourceArrowTarget X)
    rw [Category.assoc, cofiberRightAdjointZeroSource_target, Category.comp_id]
    exact eqToIso (congrArg (fun f => HomotopyCategory.mk (functorVertex f))
      (by rw [zeroSourceArrowTarget, ← Category.assoc, fullSubcomplexLift_ι]; rfl))
  have hi := FunctorIso.postcomp h (fullSubcomplexOnVertices _ IsZeroSourceArrow).ι
  simpa only [Category.assoc, cofiberRightAdjointZeroSource_inclusion,
    a₀, fullSubcomplexLift_ι] using hi

/-- 普遍 cofiber 関手との合成は、零始点矢印の元の終点の族と同型。 -/
def universalCofiberZeroSourceIso :
    FunctorIso (a ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X (𝟙 _)) (a ≫ _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.target X) := by
  have h := FunctorIso.postcomp (zeroSourceArrowComparison X a ha)
    (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X (𝟙 _))
  have := cofiberAdjunction_counitHom_isIso X
  have he := FunctorIso.precomp (asIso (cofiberAdjunction X).counitHom)
    (a ≫ _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.target X)
  exact h ≪≫ (by simpa only [Category.assoc, Category.comp_id] using he)

/-- 元の矢印族で選んだ cofiber も、同じ元の終点と全関手同型になる。 -/
def cofiberZeroSourceIso : FunctorIso (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.cofiber X a) (a ≫ _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.ArrowTarget.target X) :=
  CofiberFamily.compositionIso X a ≪≫ universalCofiberZeroSourceIso X a ha

end SerrePositivity.KST.LocalizingInvariants
