module
public import SerrePositivity.KST.SConstruction.PointedKanEnrichedEquivalences
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomEquivalence

/-! # 点つき写像の元の成分と coherent nerve の射の忠実な比較
概要：点つき Kan 模型間の元のホモトピー成分を、coherent nerve のホモトピー圏から反映する。
方針：豊穣 Hom 比較の π₀ 全単射と、右写像空間の π₀ による射の表示を使う。
規約：coherent な可逆性だけから元の点つき成分の一致を推測しない。
使われ方：図式全体で選んだ逆・延長と、既存の構造射との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 宇宙を持ち上げても零次の成分の等式は元の宇宙へ反映できる。 -/
lemma piZero_ulift_reflect {K : SSet.{u}} {x y : K _⦋0⦌}
    (h : SSet.π₀.mk (X := (SSet.uliftFunctor.{v, u}).obj K) (ULift.up x) =
      SSet.π₀.mk (ULift.up y)) : SSet.π₀.mk x = SSet.π₀.mk y := by
  have hh := (SSet.π₀.mk_eq_mk_iff _ _).mp h
  have hd {a b : ((SSet.uliftFunctor.{v, u}).obj K) _⦋0⦌}
      (r : Relation.EqvGen SSet.π₀Rel a b) : SSet.π₀.mk a.down = SSet.π₀.mk b.down := by
    induction r with
    | rel a b hab =>
      obtain ⟨e⟩ := hab
      exact SSet.π₀.sound (SSet.Edge.mk e.edge.down
        (congrArg ULift.down e.src_eq) (congrArg ULift.down e.tgt_eq))
    | refl _ => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih hk => exact ih.trans hk
  exact hd hh

/-- 元の点つき射が coherent nerve のホモトピー圏で表す射。 -/
def pointedKanHomotopyClass {X Y : PointedKanObject.{u}} (f : X ⟶ Y) :=
  SSet.Truncated.HomotopyCategory.homMk
    (V := (truncation 2).obj PointedKanInfinity.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated

/-- 元の射の類は豊穣 Hom 比較と右写像空間の π₀ 表示を経由する。 -/
lemma pointedKanHomotopyClass_comparison {X Y : PointedKanObject.{u}} (f : X ⟶ Y) :
    pointedKanHomotopyClass f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y)
        (SSet.π₀.mk (ULift.up (SimplicialCategory.homEquiv' X Y f)))) := by
  change SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f).toTruncated =
    SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv _ _
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y).app (Opposite.op ⦋0⦌)
        (ULift.up (SimplicialCategory.homEquiv' X Y f))))
  apply congrArg SSet.Truncated.HomotopyCategory.homMk
  apply SSet.Truncated.Edge.ext
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_ordinary f).symm

/-- coherent nerve の射の等号は、元の点つき写像空間の成分の等号と同値。 -/
lemma pointedKanHomotopyClass_eq_iff {X Y : PointedKanObject.{u}} (f g : X ⟶ Y) :
    pointedKanHomotopyClass f = pointedKanHomotopyClass g ↔
      componentOf f.hom = componentOf g.hom := by
  constructor
  · intro h
    rw [pointedKanHomotopyClass_comparison, pointedKanHomotopyClass_comparison] at h
    have hh := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroToHom_injective (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y)) h
    have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison_isSimplicialHomotopyEquivalence X Y).mapPiZero_bijective.injective hh
    have hd := piZero_ulift_reflect hi
    rw [pointedKanObject_vertex_eq, pointedKanObject_vertex_eq] at hd
    exact hd
  · intro h
    obtain ⟨e⟩ := pointedKanObject_nonempty_vertexIso_of_component f g h
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveEdge_homMk_eq_of_enrichedVertexIso e

/-- 元の恒等射の coherent な類は恒等射。 -/
lemma pointedKanHomotopyClass_id (X : PointedKanObject.{u}) :
    pointedKanHomotopyClass (𝟙 X) = 𝟙 (SSet.Truncated.HomotopyCategory.mk
      (V := (truncation 2).obj PointedKanInfinity.{u}) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X)) := by
  dsimp only [pointedKanHomotopyClass]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, SSet.Edge.toTruncated_id,
    SSet.Truncated.HomotopyCategory.homMk_id]

/-- 元の射の合成と coherent nerve のホモトピー圏での合成は一致する。 -/
lemma pointedKanHomotopyClass_comp {X Y Z : PointedKanObject.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    pointedKanHomotopyClass f ≫ pointedKanHomotopyClass g = pointedKanHomotopyClass (f ≫ g) :=
  SSet.Truncated.HomotopyCategory.homMk_comp_homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveCompStruct f g).toTruncated

/-- 指定三辺を保つ coherent な実三角形から、元の点つき写像の合成成分を反映する。 -/
lemma pointedKanObject_component_comp_of_triangle {X Y Z : PointedKanObject.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
    (t : SSet.Edge.CompStruct (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge h)) :
    componentOf (f.hom ≫ g.hom) = componentOf h.hom := by
  apply (pointedKanHomotopyClass_eq_iff (f ≫ g) h).mp
  exact (pointedKanHomotopyClass_comp f g).symm.trans
    (SSet.Truncated.HomotopyCategory.homMk_comp_homMk t.toTruncated)

end SerrePositivity.KST.SConstruction
