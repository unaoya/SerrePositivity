module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFiberPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeRestrictionTransport
public import SerrePositivity.InfinityCategories.F1B.Fibrations.TrivialFibrationHomotopy
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-!
概要：固定辺の余錐の終点制限の切断を固定終点の fiber に移し、始点制限との比較を構成する。
方針：終点を保つ切断と、終点評価上の恒等族とのホモトピーを使う。
規約：比較は指定した辺と元の coslice の切断を保持する。使われ方：span の Hom の cospan の表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X : SSet.{u}} [Quasicategory X] (e : (Δ[1] : SSet.{u}) ⟶ X)

/-- 辺全体への余錐の延長は可変終点の射影を厳密に保つ。 -/
lemma cosliceEdgeSection_projection :
    cosliceEdgeSection e ≫ sliceUnderProjection e =
      sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e) := by
  rw [← sliceUnderRestrict_projection e (stdSimplex.δ (0 : Fin 2)),
    ← Category.assoc, cosliceEdgeSection_target, Category.id_comp]

/-- 終点側の固定終点余錐空間から、辺全体の余錐空間への指定した切断。 -/
def cosliceEdgeSectionFiber (y : X _⦋0⦌) :
    coconeMappingSpace (stdSimplex.δ (0 : Fin 2) ≫ e) y ⟶ coconeMappingSpace e y :=
  vertexFiberMap _ _ (cosliceEdgeSection e) (cosliceEdgeSection_projection e) y

/-- 固定終点の切断を元の coslice に含めると、元の延長族を回収する。 -/
lemma cosliceEdgeSectionFiber_ι (y : X _⦋0⦌) :
    cosliceEdgeSectionFiber e y ≫ vertexFiberι (sliceUnderProjection e) y =
      vertexFiberι (sliceUnderProjection (stdSimplex.δ (0 : Fin 2) ≫ e)) y ≫ cosliceEdgeSection e :=
  vertexFiberMap_ι _ _ _ _ _

/-- 固定終点の切断も終点側への制限の厳密な切断。 -/
lemma cosliceEdgeSectionFiber_target (y : X _⦋0⦌) :
    cosliceEdgeSectionFiber e y ≫ cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y =
      𝟙 _ := by
  apply vertexFiber_hom_ext
  rw [Category.assoc, cosliceRestrictionFiberMap, vertexFiberMap_ι,
    ← Category.assoc, cosliceEdgeSectionFiber_ι, Category.assoc,
    cosliceEdgeSection_target, Category.comp_id, Category.id_comp]

/-- 終点制限の指定した切断は、固定終点でも実際のホモトピー同値。 -/
lemma cosliceEdgeSectionFiber_homotopyEquivalence (y : X _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (cosliceEdgeSectionFiber e y) := by
  have : KanComplex (coconeMappingSpace e y) := coconeMappingSpace_kanComplex _ _
  have : KanComplex (coconeMappingSpace (stdSimplex.δ (0 : Fin 2) ≫ e) y) :=
    coconeMappingSpace_kanComplex _ _
  have := cosliceTriangleTarget_trivialKanFibration e y
  have hp := isQCatEquivalence_of_trivialKanFibration
    (E := coconeMappingSpace e y) (B := coconeMappingSpace (stdSimplex.δ (0 : Fin 2) ≫ e) y)
    (cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y)
  have hs : IsQCatEquivalence (cosliceEdgeSectionFiber e y) := by
    apply hp.cancel_right
    rw [cosliceEdgeSectionFiber_target]
    exact (qCatEquivalenceOfIso (Iso.refl _)).isQCatEquivalence
  exact hs.isSimplicialHomotopyEquivalence

/-- 切断の始点側への制限は、実際の辺による固定終点の Hom の前合成そのもの。 -/
lemma cosliceEdgeSectionFiber_source (a : (Δ[0] : SSet.{u}) ⟶ X)
    (ha : stdSimplex.δ (1 : Fin 2) ≫ e = a) (y : X _⦋0⦌) :
    cosliceEdgeSectionFiber e y ≫
        normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2)) ha y =
      cosliceEdgeFiberPrecomposition e a (stdSimplex.δ (0 : Fin 2) ≫ e) ha rfl y := by
  apply vertexFiber_hom_ext
  rw [Category.assoc, normalizedCoconeRestrictionFiber, vertexFiberMap_ι,
    ← Category.assoc, cosliceEdgeSectionFiber_ι, cosliceEdgeFiberPrecomposition_ι]
  simp only [cosliceEdgePrecompositionAt, cosliceEdgePrecomposition,
    normalizedCoconeRestriction, eqToHom_refl, Category.id_comp, Category.assoc]

/-- 辺全体の余錐の始点制限は、終点制限と実際の辺の前合成との合成に全単体でホモトピック。 -/
lemma cosliceEdgeRestriction_precomposition_homotopy (a : (Δ[0] : SSet.{u}) ⟶ X)
    (ha : stdSimplex.δ (1 : Fin 2) ≫ e = a) (y : X _⦋0⦌) :
    Nonempty (SSet.Homotopy
      (normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2)) ha y)
      (cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y ≫
        cosliceEdgeFiberPrecomposition e a (stdSimplex.δ (0 : Fin 2) ≫ e) ha rfl y)) := by
  have := cosliceTriangleTarget_trivialKanFibration e y
  obtain ⟨H, _⟩ := exists_homotopy_over_trivialKanFibration
    (cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y)
    (𝟙 _) (cosliceRestrictionFiberMap e (stdSimplex.δ (0 : Fin 2)) y ≫
      cosliceEdgeSectionFiber e y) (by
        rw [Category.id_comp, Category.assoc, cosliceEdgeSectionFiber_target]
        erw [Category.comp_id])
  have h := functorHomotopyPostcomp H
    (normalizedCoconeRestrictionFiber e (stdSimplex.δ (1 : Fin 2)) ha y)
  simpa only [Category.id_comp, Category.assoc, cosliceEdgeSectionFiber_source] using
    (show Nonempty (SSet.Homotopy _ _) from ⟨h⟩)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
