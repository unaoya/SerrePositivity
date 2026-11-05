module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.F1.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.Stable.SpecifiedCofiberSpan

/-!
概要：元の任意の矢印族を、第二枝の終点が零である span の全単体族へ延長する。
方針：零対象へ向かう辺の始点評価の厳密な切断を使う。
規約：元の第一枝を厳密に保持する。使われ方：全単体上の差の cofiber 関手。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
namespace SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily
open SerrePositivity.KST.LocalizingInvariants.CofiberFamily

variable (X : SSet.{u}) [Quasicategory X] [IsStable X]

def zeroArrowSection : X ⟶ zeroTargetArrows X :=
  Classical.choose (trivialKanFibration_exists_section (zeroTargetArrowSource X))

lemma zeroArrowSection_source : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrowSection X ≫ zeroTargetArrowSource X = 𝟙 X :=
  Classical.choose_spec (trivialKanFibration_exists_section (zeroTargetArrowSource X))

variable {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)

def zeroArrow : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  (a ≫ evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrowSection X ≫
    (fullSubcomplexOnVertices _ IsZeroTargetArrow).ι

lemma zeroArrow_source : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrow X a ≫
    evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      a ≫ evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  change (_ ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrowSection X ≫ (fullSubcomplexOnVertices _ IsZeroTargetArrow).ι) ≫ _ = _
  change (_ ≫ _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrowSection X) ≫ zeroTargetArrowSource X = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrowSection_source, Category.comp_id]

def span : A ⟶ (ihom (horn 2 0 : SSet.{u})).obj X :=
  stable_spanFamilyOfArrows a (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrow X a) (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrow_source X a).symm

lemma span_left : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span X a ≫ (pre horn₂₀.ι₀₁).app X = a := stable_spanFamilyOfArrows_left _ _ _

lemma span_right : _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span X a ≫ (pre horn₂₀.ι₀₂).app X = _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrow X a :=
  stable_spanFamilyOfArrows_right _ _ _

lemma span_vertex_zero (x : A _⦋0⦌) :
    IsZeroVertex ((horn₂₀.ι₀₂ ≫
      (functorVertexEquiv (horn 2 0 : SSet.{u}) X).symm ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span X a).app _ x)).app
        (Opposite.op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  let d := (functorVertexEquiv (horn 2 0 : SSet.{u}) X).symm ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span X a).app _ x)
  have hd : functorVertex d = (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span X a).app _ x :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change IsZeroVertex ((evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
    (Opposite.op ⦋0⦌) (functorVertex (horn₂₀.ι₀₂ ≫ d)))
  change IsZeroVertex ((evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
    (Opposite.op ⦋0⦌) (((pre horn₂₀.ι₀₂).app X).app _ (functorVertex d)))
  rw [hd]
  change IsZeroVertex (((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span X a ≫ (pre horn₂₀.ι₀₂).app X) ≫
    evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app _ x)
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span_right]
  exact fullSubcomplexOnVertices_vertex
    ((a ≫ evaluateFunctorAt (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
      _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrowSection X).app _ x)

lemma span_hasColimit (x : A _⦋0⦌) :
    HasColimit ((functorVertexEquiv (horn 2 0 : SSet.{u}) X).symm ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span X a).app _ x)) :=
  hasColimit_span_of_zero_second _ (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span_vertex_zero X a x)

end SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.span := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.span_hasColimit := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span_hasColimit

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.span_left := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.span_right := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.span_vertex_zero := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span_vertex_zero

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrow (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroArrow := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrow

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrowSection (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroArrowSection := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrowSection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroArrowSection_source := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrowSection_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroArrow_source := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrow_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.span._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.span._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroArrow._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrow._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.CofiberFamily.zeroArrowSection._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.zeroArrowSection._proof_1
