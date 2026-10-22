module
public import SerrePositivity.KST.Fibration.SpaceLocalizationPreFaithful
public import SerrePositivity.KST.Fibration.SpaceDiagramLocalizationDescent
public import SerrePositivity.InfinityCategories.F1.UniverseInvertibleEdge

/-! # 元の小さい商局所化の、宇宙を揃えた空間値関手 ∞ 圏での普遍性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

/-- 同じ指定辺の反転は、実際の可逆辺とその逆データの宇宙持ち上げで保たれる。 -/
theorem invertsEdges_ulift {X Q : SSet.{u}} [Quasicategory Q] (q : X ⟶ Q)
    (W : Set (X _⦋1⦌)) (hq : InvertsEdges q W) :
    InvertsEdges ((SSet.uliftFunctor.{u + 1, u}).map q) (ULift.up '' W) := by
  rintro s ⟨t, ht, rfl⟩
  have hi := IsInvertibleEdge.ulift.{u, u + 1} (hq ht)
  exact (isInvertibleEdge_congr (show
    (uliftTruncatedEdge ((edgeOfSimplex t).map ((truncation 2).map q))).edge =
      ((edgeOfSimplex (ULift.up t)).map
        ((truncation 2).map ((SSet.uliftFunctor.{u + 1, u}).map q))).edge from rfl)).mp hi

variable {X Q : SSet.{u}} [Quasicategory Q] (q : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hq : IsLocalization q W)

/-- 元の商への前合成を、空間値の全反転関手の実際の全部分複体に値を取る射として保持する。 -/
def spaceLocalizationPrecomposition :
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj Q)).obj SpaceInfinity.{u} ⟶
      invertingFunctors ((SSet.uliftFunctor.{u + 1, u}).obj X) SpaceInfinity.{u} (ULift.up '' W) :=
  localizationPrecomposition ((SSet.uliftFunctor.{u + 1, u}).map q) (ULift.up '' W)
    (invertsEdges_ulift q W hq.choose) SpaceInfinity

/-- 空間値関手 ∞ 圏での元の局所化普遍性。全写像空間の充満忠実性と実因子化から証明する。 -/
theorem spaceLocalizationPrecomposition_isQCatEquivalence :
    IsQCatEquivalence (spaceLocalizationPrecomposition q W hq) := by
  let k := (SSet.uliftFunctor.{u + 1, u}).map q
  let V : Set (((SSet.uliftFunctor.{u + 1, u}).obj X) _⦋1⦌) := ULift.up '' W
  have hi := isFullyFaithful_fullSubcomplexOnVertices_ι
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj X)).obj SpaceInfinity)
    (IsInvertingFunctorVertex ((SSet.uliftFunctor.{u + 1, u}).obj X) SpaceInfinity V)
  have hc : spaceLocalizationPrecomposition q W hq ≫
      (invertingFunctors ((SSet.uliftFunctor.{u + 1, u}).obj X) SpaceInfinity V).ι =
        (pre k).app SpaceInfinity :=
    localizationPrecomposition_ι k V (invertsEdges_ulift q W hq.choose) SpaceInfinity
  apply isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
  · apply hi.cancel_right
    exact Eq.mpr (congrArg (fun m => IsFullyFaithful m) hc)
      (spaceLocalizationPre_fullyFaithful q W hq)
  · intro v
    obtain ⟨H, hH⟩ := (functorVertexEquiv
      ((SSet.uliftFunctor.{u + 1, u}).obj X) SpaceInfinity).surjective v.val
    have hv := fullSubcomplexOnVertices_vertex v
    change InvertsEdges ((functorVertexEquiv _ _).symm v.val) V at hv
    rw [← hH, Equiv.symm_apply_apply] at hv
    let K := spaceDiagramLocalizationDescend q W hq H hv
    have e : FunctorIso (k ≫ K) H := spaceDiagramLocalizationDescendIso q W hq H hv
    have he := e ≪≫ eqToIso (congrArg HomotopyCategory.mk hH)
    exact ⟨functorVertex K, ⟨hi.preimageVertexIso he⟩⟩

end SerrePositivity.KST.Fibration
