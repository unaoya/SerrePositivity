module
public import SerrePositivity.KST.SConstruction.FamilyChainWitnessPrecomposition

/-! # 元の全合成木を標的写像で保持する
概要：実補正列の全合成証人を後合成し、元の全区間と全三角形の像を保持する。
方針：内部 Hom の後合成で元の全二単体を写し、同じ全円柱の辺へ表示を合わせる。
規約：合成木を選び直さず、元の同じ全木の像を保持する。
使われ方：合成補正の二つの部分を、元の単一射補正の全木から構成する。
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

/-- 元の全円柱の後合成像は、同じ元の円柱を後合成した実辺そのもの。 -/
lemma familyHomotopyEdge_postcomp {U E B : SSet.{u}} (p : E ⟶ B)
    {f g : U ⟶ E} (H : SSet.Homotopy f g) :
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)).map ((ihom U).map p)).edge =
      (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H p))).edge := by
  apply SSet.yonedaEquiv.symm.injective
  rw [SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp]
  change curry H.h ≫ (ihom U).map p = curry (H.h ≫ p)
  rw [curry_natural_right]

/-- 元の全区間と全三角形を同じ後合成で写した実合成木。 -/
def familyChainWitnessPostcomp {U E B : SSet.{u}} (p : E ⟶ B)
    {f g : U ⟶ E} {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) :
    FamilyChainCompositionWitness (familyHomotopyChainMap c p) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H p) := by
  induction w with
  | nil f =>
      have h : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (f ≫ p) = _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl f) p := by
        apply SSet.RelativeMorphism.Homotopy.ext
        exact (Category.assoc _ _ _).symm
      exact familyChainWitnessHomTransport (.nil (f ≫ p)) h
  | cons a tail tailWitness triangle ih =>
      exact .cons (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp a p) (familyHomotopyChainMap tail p) ih
        ((triangle.map ((ihom U).map p)).ofEq (familyHomotopyEdge_postcomp p a)
          (familyHomotopyEdge_postcomp p _) (familyHomotopyEdge_postcomp p _))

/-- 後合成した全木の全区間は、元の全区間の同じ後合成像を同じ順序で持つ。 -/
lemma familyChainWitnessPostcomp_trace {U E B : SSet.{u}} (p : E ⟶ B)
    {f g : U ⟶ E} {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) :
    familyChainCompositionInputTrace (familyChainWitnessPostcomp p w) =
      (familyChainCompositionInputTrace w).map (· ≫ p) := by
  rw [familyChainCompositionInputTrace_eq, familyChainCompositionInputTrace_eq,
    familyHomotopyChainMap_trace]

/-- 後合成した全木の全三角形は、元の同じ全二単体の後合成像を同じ順序で持つ。 -/
lemma familyChainWitnessPostcomp_triangles {U E B : SSet.{u}} (p : E ⟶ B)
    {f g : U ⟶ E} {c : FamilyHomotopyChain f g} {H : SSet.Homotopy f g}
    (w : FamilyChainCompositionWitness c H) :
    familyChainCompositionTriangles (familyChainWitnessPostcomp p w) =
      (familyChainCompositionTriangles w).map (· ≫ p) := by
  induction w with
  | nil f =>
      rw [familyChainWitnessPostcomp, familyChainWitnessHomTransport_triangles]
      rfl
  | cons a tail tailWitness triangle ih =>
      change _ :: familyChainCompositionTriangles (familyChainWitnessPostcomp p tailWitness) =
        _ :: (familyChainCompositionTriangles tailWitness).map _
      rw [ih]
      congr 1

end SerrePositivity.KST.SConstruction
