module

public import SerrePositivity.KST.Spectra.CofiberMappingFiberIso
public import SerrePositivity.KST.Spectra.PointedCofiberUniversal
public import SerrePositivity.KST.Spectra.PointedVerticalPaths
public import SerrePositivity.KST.Spectra.LoopMappingOperations

/-!
概要：指定部分で零に固定したホモトピーを、元の二つの cofiber 降下射の間へ降ろす。
方針：区間族を制限射の厳密な基点 fiber へ持ち上げ、既存の cofiber–Hom 同型で戻す。
規約：Kan 性も部分対象の単射性も不要。使われ方：相対パラメータ族の写像類の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- cofiber からの Hom の族は、元の商射への制限で決まる。 -/
lemma cofiber_pre_hom_ext {A B E : PointedSimplicialSet.{u}} (j : B ⟶ A)
    {T : SSet.{u}} {f g : T ⟶ (PointedObject.basedHom (pointedCofiber j) E).right}
    (h : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pointedCofiberProjection j) E =
      g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pointedCofiberProjection j) E) : f = g := by
  apply (cancel_mono (cofiberMappingFiberIso j E).hom).1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j E) (PointedSimplicialSet.basepoint (PointedObject.basedHom B E))
  simpa only [Category.assoc, cofiberMappingFiberIso_hom_ι] using h

/-- 点の族への前合成は元の点つき射への前合成に一致する。 -/
lemma pointFamily_pre {A B E : PointedSimplicialSet.{u}} (j : B ⟶ A) (f : A ⟶ E) :
    pointFamily f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j E = pointFamily (j ≫ f) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  exact familyVertex_pre j f

variable {A B E : PointedSimplicialSet.{u}} (j : B ⟶ A) {f g : A ⟶ E}
  (hf : j ≫ f = 0) (hg : j ≫ g = 0) (H : SSet.Homotopy f.right g.right)
  (hbase : A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
    toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom)
  (hrel : j.right ▷ (Δ[1] : SSet.{u}) ≫ H.h =
    toUnit (B.right ⊗ (Δ[1] : SSet.{u})) ≫ E.hom)

include hrel in
/-- 相対零ホモトピーの区間族は制限射の厳密な基点上にある。 -/
lemma paramCurry_restriction_zero :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry A E H.h hbase ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j E =
      SSet.const (PointedSimplicialSet.basepoint (PointedObject.basedHom B E)) := by
  rw [← familyVertex_zero B E]
  apply (cancel_mono (PointedObject.basedHomι B E)).1
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι]
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, uncurry_const_familyVertex,
    PointedObject.zero_right, comp_toUnit_assoc]
  exact hrel

/-- 元の区間族を cofiber からの Hom へ降ろす。 -/
def cofiberInterval : (Δ[1] : SSet.{u}) ⟶
    (PointedObject.basedHom (pointedCofiber j) E).right :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre j E) (PointedSimplicialSet.basepoint (PointedObject.basedHom B E))
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry A E H.h hbase) (paramCurry_restriction_zero j H hbase hrel) ≫
      (cofiberMappingFiberIso j E).inv

/-- cofiber 区間の制限は、入力した元の区間族そのもの。 -/
lemma cofiberInterval_restriction :
    cofiberInterval j H hbase hrel ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (pointedCofiberProjection j) E =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry A E H.h hbase := by
  dsimp only [cofiberInterval]
  rw [Category.assoc, ← cofiberMappingFiberIso_hom_ι,
    Iso.inv_hom_id_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberLift_ι]

/-- 降ろした区間は、元の二つの降下射を同じ端点として持つ。 -/
def cofiberEdge : (PointedObject.basedHom (pointedCofiber j) E).right.Edge
    (familyVertex (pointedCofiberDescOfZero j f hf))
    (familyVertex (pointedCofiberDescOfZero j g hg)) := by
  refine SSet.Edge.mk (SSet.yonedaEquiv (cofiberInterval j H hbase hrel)) ?_ ?_
  · rw [← stdSimplex.yonedaEquiv_δ_comp]
    have h : stdSimplex.δ (1 : Fin 2) ≫ cofiberInterval j H hbase hrel =
        pointFamily (pointedCofiberDescOfZero j f hf) := by
      apply cofiber_pre_hom_ext j
      rw [Category.assoc, cofiberInterval_restriction, paramCurry_homotopy_zero,
        pointFamily_pre, pointedCofiberProjection_descOfZero]
    rw [h]
    rfl
  · rw [← stdSimplex.yonedaEquiv_δ_comp]
    have h : stdSimplex.δ (0 : Fin 2) ≫ cofiberInterval j H hbase hrel =
        pointFamily (pointedCofiberDescOfZero j g hg) := by
      apply cofiber_pre_hom_ext j
      rw [Category.assoc, cofiberInterval_restriction, paramCurry_homotopy_one,
        pointFamily_pre, pointedCofiberProjection_descOfZero]
    rw [h]
    rfl

include H hbase hrel in
/-- 元の降下射の成分は、指定部分を零に固定した実際のホモトピーにより等しい。 -/
lemma componentOf_cofiberDesc_eq :
    componentOf (pointedCofiberDescOfZero j f hf) =
      componentOf (pointedCofiberDescOfZero j g hg) :=
  π₀.sound (cofiberEdge j hf hg H hbase hrel)

include H hbase hrel in
/-- 商へ降ろした同じ端点間の基点固定ホモトピー。 -/
lemma cofiberDesc_homotopy :
    ∃ W : SSet.Homotopy (pointedCofiberDescOfZero j f hf).right
        (pointedCofiberDescOfZero j g hg).right,
      (pointedCofiber j).hom ▷ (Δ[1] : SSet.{u}) ≫ W.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom :=
  ⟨homotopyOfEdge (cofiberEdge j hf hg H hbase hrel),
    homotopyOfEdge_base (cofiberEdge j hf hg H hbase hrel)⟩

end SerrePositivity.KST.Spectra.PointedMapping

namespace SerrePositivity.KST.Spectra

/-- 零合成による降下は、元の点つき射への後合成と厳密に可換。 -/
lemma pointedCofiberDescOfZero_comp {A B E F : PointedSimplicialSet.{u}} (j : B ⟶ A)
    (f : A ⟶ E) (hf : j ≫ f = 0) (p : E ⟶ F) :
    pointedCofiberDescOfZero j (f ≫ p) (by rw [← Category.assoc, hf, zero_comp]) =
      pointedCofiberDescOfZero j f hf ≫ p := by
  apply pointedCofiber_hom_ext j
  rw [pointedCofiberProjection_descOfZero, ← Category.assoc,
    pointedCofiberProjection_descOfZero]

end SerrePositivity.KST.Spectra
