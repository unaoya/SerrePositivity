module

public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteSSetProductUniversal
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteKanProductComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanConeLimits
public import SerrePositivity.InfinityCategories.F2.CatInfinity.StrictNativeConeLeg
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KanNativeConeLeg

/-!
概要：元の有限非空 Kan 族の反復積を頂点とする native な積錐。
方針：元の全射影の通常の積錐を作り、元の台の極限性から coherent nerve へ移す。
規約：頂点は元の反復積そのもの。添字だけを元の小さい宇宙へ持ち上げる。
使われ方：sifted な底上の元の全空間 Kan 比較による有限積錐の輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の有限非空 Kan 族を、持ち上げた有限離散添字の通常の図式にする。 -/
def finiteKanProductDiagram (n : ℕ) (E : Fin (n + 1) → KanObject.{u}) :
    Discrete (ULift.{u} (Fin (n + 1))) ⥤ KanObject.{u} :=
  Discrete.functor (fun i ↦ E i.down)

/-- 元の Kan 族の台の反復積を、同じ Kan 対象に束ねる。 -/
def finiteKanProductObject (n : ℕ) (E : Fin (n + 1) → KanObject.{u}) : KanObject.{u} :=
  ⟨nonemptyFiniteSSetProduct n (fun i ↦ (E i).obj),
    nonemptyFiniteSSetProduct_kanComplex n _ (fun _ ↦ inferInstance)⟩

/-- 元の反復積と元の全射影の通常の錐。 -/
def finiteKanProductCone (n : ℕ) (E : Fin (n + 1) → KanObject.{u}) :
    Cone (finiteKanProductDiagram n E) where
  pt := finiteKanProductObject n E
  π := Discrete.natTrans (fun i ↦ nonemptyFiniteSSetProjection n (fun j ↦ (E j).obj) i.as.down)

/-- 元の通常の全射影の錐は、台の単体集合の積錐。 -/
def finiteKanProductCone_forget_isLimit (n : ℕ) (E : Fin (n + 1) → KanObject.{u}) :
    IsLimit (kanObjectForget.mapCone (finiteKanProductCone n E)) where
  lift s := nonemptyFiniteSSetLift n (fun i ↦ s.π.app (Discrete.mk (ULift.up i)))
  fac s i := nonemptyFiniteSSetLift_projection n _ i.as.down
  uniq s f hf := nonemptyFiniteSSetProduct_hom_ext n _ (fun i ↦ by
    exact (hf (Discrete.mk (ULift.up i))).trans
      (nonemptyFiniteSSetLift_projection n
        (E := fun j ↦ (E j).obj) (fun j ↦ s.π.app (Discrete.mk (ULift.up j))) i).symm)

/-- 元の反復積を頂点とする有限非空 Kan 図式の native な全錐。 -/
def finiteKanProductNativeCone (n : ℕ) (E : Fin (n + 1) → KanObject.{u}) :
    JoinCone (kanDiagramCoherentNerve (finiteKanProductDiagram n E)) :=
  (strictCoherentCone (finiteKanProductCone n E)).cast
    (strictCoherentDiagram_eq_kanDiagram (finiteKanProductDiagram n E))

/-- 元の finite 積錐の頂点は元の反復積 Kan 対象の標準頂点そのもの。 -/
lemma finiteKanProductNativeCone_vertex (n : ℕ) (E : Fin (n + 1) → KanObject.{u}) :
    (finiteKanProductNativeCone n E).vertex = coherentNerveVertex (finiteKanProductObject n E) := by
  rw [finiteKanProductNativeCone, JoinCone.vertex_cast, strictCoherentCone_vertex]
  rfl

/-- 元の反復積を頂点とする全錐は、実際の native な有限非空積錐。 -/
lemma finiteKanProductNativeCone_isLimit (n : ℕ) (E : Fin (n + 1) → KanObject.{u}) :
    IsLimitCone (finiteKanProductNativeCone n E) := by
  apply IsLimitCone.cast
  exact strictCoherentCone_isLimit_of_discrete_homLimit (finiteKanProductCone n E)
    (kanObjectHomCone_isLimit_of_forget _ (finiteKanProductCone_forget_isLimit n E))

/-- 元の有限積錐の native な全脚は、元の通常の射影の全一単体。 -/
lemma finiteKanProductNativeCone_leg_edge (n : ℕ) (E : Fin (n + 1) → KanObject.{u})
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    (F2.nativeConeLeg (finiteKanProductNativeCone n E)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (coherentNerveEdge ((finiteKanProductCone n E).π.app i)).edge :=
  F2.nativeConeLeg_strict (finiteKanProductCone n E) i

/-- 元の有限積錐の native な脚を戻すと、元の通常の射影そのもの。 -/
lemma finiteKanProductNativeCone_kanLeg (n : ℕ) (E : Fin (n + 1) → KanObject.{u})
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    F2.kanNativeConeLeg (finiteKanProductNativeCone n E) (finiteKanProductObject n E)
      (finiteKanProductNativeCone_vertex n E) i = (finiteKanProductCone n E).π.app i := by
  have h : F2.kanNativeConeLegEdge (finiteKanProductNativeCone n E) (finiteKanProductObject n E)
      (finiteKanProductNativeCone_vertex n E) i =
        coherentNerveEdge ((finiteKanProductCone n E).π.app i) := by
    apply SSet.Edge.ext
    exact finiteKanProductNativeCone_leg_edge n E i
  exact (congrArg coherentNerveEdgeToHom h).trans (coherentNerveEdgeToHom_edge _)

end SerrePositivity.InfinityCategories.HomotopyLimits
