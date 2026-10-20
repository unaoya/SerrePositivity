module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftBranchHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomPostcomp
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramRestriction

/-!
概要：左枝の初期 Hom 族の共通部分への制限を、元の根辺三角形の中頂点の族へ同定する。
方針：同じ終端辺族を保つ厳密な制限と初期 Hom の後合成自然性を使う。
規約：始点を始対象 c と取り違えない。使われ方：枝と根辺の比較円柱の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "qB" => sliceUnderProjection (i ≫ p)
local notation "qA" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "r" => sliceUnderRestrict (i ≫ p) f
local notation "b" => ConcreteCategory.hom
  (NatTrans.app (sliceUnderRestrict (i ≫ p) f) (Opposite.op ⦋0⦌)) dB
local notation "k" => specifiedCoconeLeftTransportEdge hp p c hc dB dC
local notation "s" => specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "F" => specifiedCoconeLeftFullHomFamily hp p c hc dB dC y
local notation "G" => specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y
local notation "v" => (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3))

/-- 元の左根辺三角形の中頂点は、左枝の始点を共通部分へ制限した同じ点。 -/
lemma specifiedCoconeLeftRootedTriangle_middle : v ≫ s = SSet.yonedaEquiv.symm b := by
  have hv : stdSimplex.δ (1 : Fin 2) ≫ (SSet.yonedaEquiv.symm (k).edge ≫ r) =
      SSet.yonedaEquiv.symm b :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ r) (SSet.Edge.δ_one_yonedaEquiv_symm k)).trans
        (SSet.yonedaEquiv_symm_comp dB r))
  exact (Category.assoc (stdSimplex.δ (1 : Fin 2)) (stdSimplex.δ (0 : Fin 3)) s).trans
    ((congrArg (stdSimplex.δ (1 : Fin 2) ≫ ·)
      (specifiedCoconeLeftRootedTriangle_second hp p c hc dB dC)).trans hv)

/-- 左枝の初期 Hom 族を、同じ底上の共通部分への制限関手で写す。 -/
def specifiedCoconeLeftBranchCommonInitialFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      leftFibrationInitialTotal qA b y :=
  specifiedCoconeLeftBranchInitialHomFamily hp p c hc dB dC y ≫
    leftFibrationInitialTotalMap qB qA r (sliceUnderRestrict_projection (i ≫ p) f) dB b rfl y

/-- 同じ根辺三角形の終端辺族の uncurry は、元の左全辺族の共通部分への像である。 -/
lemma specifiedCoconeLeftRootedHomFamily_terminal_uncurry :
    joinMap (stdSimplex.δ (0 : Fin 3)) (𝟙 _) ≫ sliceUnderUncurry G =
      sliceUnderUncurry F ≫ r := by
  have h := congrArg (fun z ↦ sliceUnderUncurry z)
    (specifiedCoconeLeftRootedHomFamily_terminal hp p c hc dB dC y)
  rw [sliceUnderUncurry_restrict, specifiedCoconeLeftTerminalHomFamily,
    sliceUnderUncurry_eqToHom (specifiedCoconeLeftRootedTriangle_second hp p c hc dB dC).symm,
    specifiedCoconeLeftCommonEdgeFamily, sliceUnderUncurry_postcomp] at h
  exact h

/-- 左枝から制限した初期 Hom 族は、同じ元の根辺三角形の中頂点制限と厳密に一致する。 -/
lemma specifiedCoconeLeftBranchCommonInitialFamily_triangle :
    specifiedCoconeLeftBranchCommonInitialFamily hp p c hc dB dC y =
      initialDiagramHomFamily qA b s v
        (specifiedCoconeLeftRootedTriangle_middle hp p c hc dB dC) y G
        (specifiedCoconeLeftRootedHomFamily_fixed hp p c hc dB dC y) := by
  have hv : stdSimplex.δ (1 : Fin 2) ≫ (SSet.yonedaEquiv.symm (k).edge ≫ r) =
      SSet.yonedaEquiv.symm b :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ r) (SSet.Edge.δ_one_yonedaEquiv_symm k)).trans
        (SSet.yonedaEquiv_symm_comp dB r))
  change initialDiagramHomFamily qB dB (SSet.yonedaEquiv.symm (k).edge)
    (stdSimplex.δ (1 : Fin 2)) (SSet.Edge.δ_one_yonedaEquiv_symm k) y F
      (pointRestrictionFullEdgeFamily_fixed (sliceUnderProjection p) qB (sliceUnderRestrict p i)
        (sliceUnderRestrict_projection p i)
        (partialColimitSpecifiedPathCocone hp p c hc dB dC) k y) ≫
      leftFibrationInitialTotalMap qB qA r
        (sliceUnderRestrict_projection (i ≫ p) f) dB b rfl y = _
  rw [initialDiagramHomFamily_postcomp qB qA r
    (sliceUnderRestrict_projection (i ≫ p) f) dB b rfl (SSet.yonedaEquiv.symm (k).edge)
    (stdSimplex.δ (1 : Fin 2)) (SSet.Edge.δ_one_yonedaEquiv_symm k) hv y F
    (pointRestrictionFullEdgeFamily_fixed (sliceUnderProjection p) qB (sliceUnderRestrict p i)
      (sliceUnderRestrict_projection p i)
      (partialColimitSpecifiedPathCocone hp p c hc dB dC) k y)]
  apply vertexFiber_hom_ext (sliceUnderProjection (SSet.yonedaEquiv.symm b) ≫ qA) y
  rw [initialDiagramHomFamily, vertexFiberLift_ι, initialDiagramHomFamily, vertexFiberLift_ι]
  apply sliceUnderUncurry_injective (SSet.yonedaEquiv.symm b)
  rw [normalizedCoconeRestriction_uncurry, sliceUnderUncurry_postcomp,
    normalizedCoconeRestriction_uncurry]
  have h := congrArg (fun z ↦ joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 _) ≫ z)
    (specifiedCoconeLeftRootedHomFamily_terminal_uncurry hp p c hc dB dC y)
  simpa only [← Category.assoc, ← joinMap_comp, Category.id_comp] using h.symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
