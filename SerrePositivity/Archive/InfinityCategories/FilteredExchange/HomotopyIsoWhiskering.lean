module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyIsoTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerHom
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.WeakHomotopyPrecomposition

/-!
概要：指定円柱の同型の前後合成と、弱同値による前合成の忠実性。
方針：円柱の辺の類を写像空間のホモトピー圏の関手へ移す。
規約：指定された同型を保持。使われ方：単位上で一致する path 類を Kan 延長後へ反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定円柱の前合成の同型は元の同型の前合成。
方針：元の辺の類の前合成式。規約：指定値の等式。使われ方：単位上の同型比較。 -/
lemma homotopyIso_precomp {A X Y : SSet.{u}} [KanComplex Y]
    {f g : X ⟶ Y} (H : SSet.Homotopy f g) (a : A ⟶ X) :
    functorIsoOfSimplicialHomotopy (functorHomotopyPrecomp H a) =
      (functorIsoOfSimplicialHomotopy H).precomp a := by
  apply Iso.ext
  exact functorHomotopyPrecomp_hom H a

/-- 概要：指定円柱の後合成の同型は元の同型の後合成。
方針：元の辺の類の後合成式。規約：指定値の等式。使われ方：頂点表示の移送。 -/
lemma homotopyIso_postcomp {A X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f g : A ⟶ X} (H : SSet.Homotopy f g) (q : X ⟶ Y) :
    functorIsoOfSimplicialHomotopy (functorHomotopyPostcomp H q) =
      (functorIsoOfSimplicialHomotopy H).postcomp q := by
  apply Iso.ext
  rw [functorIso_postcomp_hom]
  exact functorHomotopyPostcomp_hom H q

/-- 概要：弱同値による Kan 標的への前合成は指定関手同型の等式を反映する。
方針：前合成同値のホモトピー圏上の忠実性。
規約：同型の存在だけに弱めない。使われ方：Kan 延長の選択に依存しない指定類。 -/
lemma functorIso_precomp_injective_of_weakEquivalence {A X Y : SSet.{u}} [KanComplex Y]
    (i : A ⟶ X) (hi : IsWeakHomotopyEquivalence i) {f g : X ⟶ Y} :
    Function.Injective (fun e : FunctorIso f g => e.precomp i) := by
  have hpre := pre_isSimplicialHomotopyEquivalence_of_weakHomotopyEquivalence i hi Y
  have hp := hpre.isQCatEquivalence
  let D := (hoFunctor.map ((pre i).app Y)).toFunctor
  haveI := hp.isFullyFaithful.toHoFullyFaithful.faithful
  intro e d h
  apply Iso.ext
  apply D.map_injective
  have hh := congrArg (fun z : FunctorIso (i ≫ f) (i ≫ g) => z.hom) h
  rw [functorIso_precomp_hom, functorIso_precomp_hom] at hh
  exact hh

end SerrePositivity.InfinityCategories.F2
