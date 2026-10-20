module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRightBranchHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootedHomFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialDiagramHomPostcomp

/-!
概要：右枝の初期 Hom 族の共通部分への制限を、元の四面体の同じ枝始点の族へ同定する。
方針：終端面とその長辺の厳密な回収、初期 Hom の後合成自然性を組み合わせる。
規約：元の右比較辺・修正三角形・四面体を保持。使われ方：枝と根辺の比較円柱の整合性。
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
local notation "qC" => sliceUnderProjection (j ≫ p)
local notation "qA" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "r" => normalizedCoconeRestriction (j ≫ p) g (coconePushoutBoundary_eq hp p)
local notation "hr" => normalizedCoconeRestriction_projection (j ≫ p) g
  (coconePushoutBoundary_eq hp p)
local notation "b" => ConcreteCategory.hom (NatTrans.app r (Opposite.op ⦋0⦌)) dC
local notation "k" => SpecifiedCoconeBranchData.right (specifiedCoconeBranchData hp p c hc dB dC)
local notation "s" => specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "F" => specifiedCoconeRightFullHomFamily hp p c hc dB dC y
local notation "G" => specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y
local notation "w" => (stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4))
local notation "v" => (stdSimplex.δ (1 : Fin 2) ≫ w)

/-- 元の四面体の枝の長辺は、選んだ同じ右比較辺を共通部分へ制限したもの。 -/
lemma specifiedCoconeRootedRightTetrahedron_branchEdge :
    w ≫ s = SSet.yonedaEquiv.symm (k).edge ≫ r := by
  calc
    _ = stdSimplex.δ (1 : Fin 3) ≫ (stdSimplex.δ (0 : Fin 4) ≫ s) :=
      Category.assoc _ _ _
    _ = stdSimplex.δ (1 : Fin 3) ≫
        (specifiedCoconeRightTriangle hp p c hc dB dC ≫ r) :=
      congrArg (stdSimplex.δ (1 : Fin 3) ≫ ·)
        (specifiedCoconeRootedRightTetrahedron_terminalFace hp p c hc dB dC)
    _ = (stdSimplex.δ (1 : Fin 3) ≫ specifiedCoconeRightTriangle hp p c hc dB dC) ≫ r :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ r) (specifiedCoconeRightTriangle_longEdge hp p c hc dB dC)

/-- 四面体の同じ枝の始点は、元の右枝始点の共通部分への像そのもの。 -/
lemma specifiedCoconeRootedRightTetrahedron_branchSource : v ≫ s = SSet.yonedaEquiv.symm b :=
  (Category.assoc (stdSimplex.δ (1 : Fin 2)) w s).trans
    ((congrArg (stdSimplex.δ (1 : Fin 2) ≫ ·)
      (specifiedCoconeRootedRightTetrahedron_branchEdge hp p c hc dB dC)).trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ r) (SSet.Edge.δ_one_yonedaEquiv_symm k)).trans
            (SSet.yonedaEquiv_symm_comp dC r))))

/-- 右枝の初期 Hom 族を、同じ底上の共通部分への制限関手で写す。 -/
def specifiedCoconeRightBranchCommonInitialFamily :
    pinchedHomLeft (partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      leftFibrationInitialTotal qA b y :=
  specifiedCoconeRightBranchInitialHomFamily hp p c hc dB dC y ≫
    leftFibrationInitialTotalMap qC qA r hr dC b rfl y

/-- 四面体族の同じ枝への制限は、元の右全辺族の共通部分への像を厳密に回収する。 -/
lemma specifiedCoconeRootedHomTetrahedronFamily_branch_uncurry :
    joinMap w (𝟙 _) ≫ sliceUnderUncurry G = sliceUnderUncurry F ≫ r := by
  have ht := congrArg (fun z ↦ sliceUnderUncurry z)
    (specifiedCoconeRootedHomTetrahedronFamily_terminalFace hp p c hc dB dC y)
  rw [sliceUnderUncurry_restrict,
    sliceUnderUncurry_eqToHom
      (specifiedCoconeRootedRightTetrahedron_terminalFace hp p c hc dB dC).symm,
    specifiedCoconeCommonHomTriangleFamily, sliceUnderUncurry_postcomp] at ht
  have hl := congrArg (fun z ↦ sliceUnderUncurry z)
    (specifiedCoconeRightHomTriangleFamily_longEdge hp p c hc dB dC y)
  rw [sliceUnderUncurry_restrict, specifiedCoconeRightHomLongEdgeFamily,
    sliceUnderUncurry_eqToHom (specifiedCoconeRightTriangle_longEdge hp p c hc dB dC).symm] at hl
  have h := congrArg (fun z ↦ joinMap (stdSimplex.δ (1 : Fin 3)) (𝟙 _) ≫ z) ht
  simp only [← Category.assoc, ← joinMap_comp, Category.id_comp] at h
  exact h.trans (congrArg (· ≫ r) hl)

/-- 共通部分へ制限した右枝の初期 Hom 族は、元の四面体の同じ枝始点の制限と一致する。 -/
lemma specifiedCoconeRightBranchCommonInitialFamily_tetrahedron :
    specifiedCoconeRightBranchCommonInitialFamily hp p c hc dB dC y =
      initialDiagramHomFamily qA b s v
        (specifiedCoconeRootedRightTetrahedron_branchSource hp p c hc dB dC) y G
        (specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y) := by
  have hv : stdSimplex.δ (1 : Fin 2) ≫ (SSet.yonedaEquiv.symm (k).edge ≫ r) =
      SSet.yonedaEquiv.symm b :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ r) (SSet.Edge.δ_one_yonedaEquiv_symm k)).trans
        (SSet.yonedaEquiv_symm_comp dC r))
  change initialDiagramHomFamily qC dC (SSet.yonedaEquiv.symm (k).edge)
    (stdSimplex.δ (1 : Fin 2)) (SSet.Edge.δ_one_yonedaEquiv_symm k) y F
      (pointRestrictionFullEdgeFamily_fixed (sliceUnderProjection p) qC (sliceUnderRestrict p j)
        (sliceUnderRestrict_projection p j)
        (partialColimitSpecifiedPathCocone hp p c hc dB dC) k y) ≫
      leftFibrationInitialTotalMap qC qA r hr dC b rfl y = _
  rw [initialDiagramHomFamily_postcomp qC qA r hr dC b rfl (SSet.yonedaEquiv.symm (k).edge)
    (stdSimplex.δ (1 : Fin 2)) (SSet.Edge.δ_one_yonedaEquiv_symm k) hv y F
    (pointRestrictionFullEdgeFamily_fixed (sliceUnderProjection p) qC (sliceUnderRestrict p j)
      (sliceUnderRestrict_projection p j)
      (partialColimitSpecifiedPathCocone hp p c hc dB dC) k y)]
  apply vertexFiber_hom_ext (sliceUnderProjection (SSet.yonedaEquiv.symm b) ≫ qA) y
  rw [initialDiagramHomFamily, vertexFiberLift_ι, initialDiagramHomFamily, vertexFiberLift_ι]
  apply sliceUnderUncurry_injective (SSet.yonedaEquiv.symm b)
  rw [normalizedCoconeRestriction_uncurry, sliceUnderUncurry_postcomp,
    normalizedCoconeRestriction_uncurry]
  have h := congrArg (fun z ↦ joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 _) ≫ z)
    (specifiedCoconeRootedHomTetrahedronFamily_branch_uncurry hp p c hc dB dC y)
  simpa only [← Category.assoc, ← joinMap_comp, Category.id_comp] using h.symm

end
end SerrePositivity.InfinityCategories.HomotopyLimits
