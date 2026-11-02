module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeReindexRestrictions
public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteCoherentSpaceProducts
public import SerrePositivity.InfinityCategories.HomotopyLimits.DiscreteIndexIso

/-!
概要：元の有限 coherent 積の余極限頂点の native 積錐を一般の非空有限添字へ移す。
方針：指定全単射の元の形状同型で全錐を引き戻し、全頂点で元の図式と厳密に照合する。
規約：元の余極限頂点と各脚の全一単体を保持する。
使われ方：P_Σ の sifted 閉性で使う任意の有限離散極限錐との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable (n : ℕ) {B : SSet.{u}}
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}))
  {J : Type u} (e : J ≃ ULift.{u} (Fin (n + 1)))

/-- 元の各余極限 Kan 対象を、指定された元の離散添字で表示する。 -/
def reindexedFiniteProductDiagram : Discrete J ⥤ KanObject.{u} :=
  Discrete.functor (fun j ↦ F2.coherentDiagramTotalKanObject (F (e j).down))

/-- 元の全単射による図式の前合成は、元の各因子を再添字した全図式そのもの。 -/
lemma reindexedFiniteProductDiagram_eq :
    (liftedDiscreteIndexIso e).hom ≫
      kanDiagramCoherentNerve (finiteKanProductDiagram n
        (fun i ↦ F2.coherentDiagramTotalKanObject (F i))) =
          kanDiagramCoherentNerve (reindexedFiniteProductDiagram n F e) := by
  apply liftedDiscreteDiagram_ext
  intro j
  change (kanDiagramCoherentNerve (finiteKanProductDiagram n
    (fun i ↦ F2.coherentDiagramTotalKanObject (F i)))).app _
      ((liftedDiscreteIndexIso e).hom.app _ (ULift.up (nerveVertex j))) = _
  rw [liftedDiscreteIndexIso_vertex, kanDiagramCoherentNerve_vertex,
    kanDiagramCoherentNerve_vertex]
  rfl

/-- 元の有限 coherent 積の余極限頂点を持つ、指定一般添字での native 積錐。 -/
def reindexedFiniteProductNativeCone [IsSiftedInfinity B] :
    JoinCone (kanDiagramCoherentNerve (reindexedFiniteProductDiagram n F e)) :=
  ((finiteSiftedCoherentProductNativeCone n F).reindexIso (liftedDiscreteIndexIso e)).cast
    (reindexedFiniteProductDiagram_eq n F e)

/-- 元の全錐の再添字は、同じ元の余極限頂点での有限積錐。 -/
lemma reindexedFiniteProductNativeCone_isLimit [IsSiftedInfinity B] :
    IsLimitCone (reindexedFiniteProductNativeCone n F e) :=
  ((isLimitCone_iff_reindexIso _ _).mp (finiteSiftedCoherentProductNativeCone_isLimit n F)).cast _

/-- 再添字した元の全錐の頂点は元の coherent 余極限頂点そのもの。 -/
lemma reindexedFiniteProductNativeCone_vertex [IsSiftedInfinity B] :
    (reindexedFiniteProductNativeCone n F e).vertex =
      coherentNerveVertex (F2.coherentDiagramTotalKanObject (finiteCoherentSpaceProduct n F)) := by
  rw [reindexedFiniteProductNativeCone, JoinCone.vertex_cast, joinCone_reindexIso_vertex,
    finiteSiftedCoherentProductNativeCone_vertex]

/-- 再添字した各 native 脚は、指定された元の脚と同じ全一単体。 -/
lemma reindexedFiniteProductNativeCone_leg_edge [IsSiftedInfinity B] (j : Discrete J) :
    (F2.nativeConeLeg (reindexedFiniteProductNativeCone n F e)
      (ULift.up (ComposableArrows.mk₀ j))).edge =
        (F2.nativeConeLeg (finiteSiftedCoherentProductNativeCone n F)
          (ULift.up (ComposableArrows.mk₀ (Discrete.mk (e j.as))))).edge := by
  change (F2.nativeConeLeg ((finiteSiftedCoherentProductNativeCone n F).reindexIso
    (liftedDiscreteIndexIso e)) _).edge = _
  rw [nativeConeLeg_reindexIso_edge]
  rfl

/-- 元の添字族を全単射で一旦標準添字に移して戻すと、元の全図式を厳密に回収する。 -/
lemma reindexedFiniteProductDiagram_original
    (G : J → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})) :
    kanDiagramCoherentNerve (reindexedFiniteProductDiagram n
      (fun i ↦ G (e.symm (ULift.up i))) e) =
        kanDiagramCoherentNerve (Discrete.functor (fun j ↦ F2.coherentDiagramTotalKanObject
          (G j))) := by
  apply liftedDiscreteDiagram_ext
  intro j
  rw [kanDiagramCoherentNerve_vertex, kanDiagramCoherentNerve_vertex]
  change spaceInfinityVertex (F2.coherentDiagramTotalKanObject
    (G (e.symm (ULift.up (e j.as).down)))) = spaceInfinityVertex _
  rw [ULift.up_down, e.symm_apply_apply]
  rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
