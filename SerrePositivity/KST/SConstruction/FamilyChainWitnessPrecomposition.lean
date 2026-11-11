module
public import SerrePositivity.KST.SConstruction.FamilyChainCompositionSquares

/-! # 元の全合成木をパラメータ制限で保持する
概要：実補正列の合成証人を前合成し、元の全区間と全合成三角形の像を保持する。
方針：内部 Hom の前合成写像で全二単体を写し、元の全比較辺との厳密な等号を使う。
規約：前合成後に合成木を選び直さず、元の同じ全木を写す。
使われ方：共有する直接補正を直通列点で照合し、元の全 trace を保持して比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 合成円柱の表示等号に沿い、元の同じ全合成木を保持する。 -/
def familyChainWitnessHomTransport {U E : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} {H K : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) (h : H = K) : FamilyChainCompositionWitness c K := by
  cases h
  exact w

/-- 円柱の表示移送でも、元の全合成三角形のリストは変わらない。 -/
lemma familyChainWitnessHomTransport_triangles {U E : SSet.{u}} {f g : U ⟶ E}
    {c : FamilyHomotopyChain f g} {H K : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) (h : H = K) :
    familyChainCompositionTriangles (familyChainWitnessHomTransport w h) =
      familyChainCompositionTriangles w := by
  cases h
  rfl

/-- 元の全比較辺の前合成像は、同じ元の円柱を前合成した辺そのもの。 -/
lemma familyHomotopyEdge_precomp {T U E : SSet.{u}} (j : T ⟶ U)
    {f g : U ⟶ E} (H : SSet.Homotopy f g) :
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)).map ((pre j).app E)).edge =
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H j))).edge := by
  apply SSet.yonedaEquiv.symm.injective
  rw [SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp]
  change curry H.h ≫ (pre j).app E = curry ((j ▷ (Δ[1] : SSet.{u})) ≫ H.h)
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_curry]

/-- 元の全区間と全三角形を同じ前合成で写す、同じ実合成木。 -/
def familyChainWitnessPrecomp {T U E : SSet.{u}} (j : T ⟶ U)
    {f g : U ⟶ E} {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) :
    FamilyChainCompositionWitness (familyHomotopyChainPrecomp j c)
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H j) := by
  induction w with
  | nil f =>
      have h : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (j ≫ f) = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl f) j := by
        apply SSet.RelativeMorphism.Homotopy.ext
        change fst T Δ[1] ≫ j ≫ f = (j ▷ (Δ[1] : SSet.{u})) ≫ fst U Δ[1] ≫ f
        exact (whiskerRight_fst_assoc j _ f).symm
      exact familyChainWitnessHomTransport (.nil (j ≫ f)) h
  | cons a tail tailWitness triangle ih =>
      exact .cons (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp a j) (familyHomotopyChainPrecomp j tail) ih
        ((triangle.map ((pre j).app E)).ofEq (familyHomotopyEdge_precomp j a)
          (familyHomotopyEdge_precomp j _) (familyHomotopyEdge_precomp j _))

/-- 前合成した合成木に記録した全区間は、元の全区間の同じ前合成像。 -/
lemma familyChainWitnessPrecomp_trace {T U E : SSet.{u}} (j : T ⟶ U)
    {f g : U ⟶ E} {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) :
    familyChainCompositionInputTrace (familyChainWitnessPrecomp j w) =
      (familyChainCompositionInputTrace w).map ((j ▷ (Δ[1] : SSet.{u})) ≫ ·) := by
  rw [familyChainCompositionInputTrace_eq, familyChainCompositionInputTrace_eq,
    familyHomotopyChainPrecomp_trace]

/-- 前合成した合成木の全三角形は、元の同じ全二単体の前合成像を同じ順序で持つ。 -/
lemma familyChainWitnessPrecomp_triangles {T U E : SSet.{u}} (j : T ⟶ U)
    {f g : U ⟶ E} {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) :
    familyChainCompositionTriangles (familyChainWitnessPrecomp j w) =
      (familyChainCompositionTriangles w).map ((j ▷ (Δ[2] : SSet.{u})) ≫ ·) := by
  induction w with
  | nil f =>
      rw [familyChainWitnessPrecomp, familyChainWitnessHomTransport_triangles]
      rfl
  | cons a tail tailWitness triangle ih =>
      change _ :: familyChainCompositionTriangles (familyChainWitnessPrecomp j tailWitness) =
        _ :: (familyChainCompositionTriangles tailWitness).map _
      rw [ih]
      congr 1

end SerrePositivity.KST.SConstruction
