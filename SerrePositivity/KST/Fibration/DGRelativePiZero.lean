module
public import SerrePositivity.KST.Fibration.DGRelativeRightArrow
public import SerrePositivity.KST.Fibration.DGKPiZeroCofinality

/-! # 相対 Verdier 四角形の元の K 右辺における π₀ 全射性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

private lemma surjective_of_iso_square {G H G' H' : CommGrpCat.{w}}
    (f : G ⟶ H) (g : G' ⟶ H') (a : G ≅ G') (b : H ≅ H')
    (h : f ≫ b.hom = a.hom ≫ g) (hf : Function.Surjective f.hom) :
    Function.Surjective g.hom := by
  intro z
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso b.hom).2 z
  obtain ⟨x, hx⟩ := hf y
  refine ⟨a.hom.hom x, ?_⟩
  have hc := congrArg (fun m : G ⟶ H' => m.hom x) h
  exact hc.symm.trans ((congrArg b.hom.hom hx).trans hy)

/-- 元の相対四角形を固定 K で写した、その右辺自体の零次 π 作用は全射。 -/
theorem dgRelativePiZeroMap_surjective (A : Type u) [CommRing A]
    (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A)) :
    Function.Surjective (((SpectrumHo.piFunctor 0).map
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareHoRight (d.square ≫ dgKInputK A))).hom) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (dgRelativeRightArrowData A d).2.2
  let t := SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow d.square)
  have he : e.edge = t.edge := dgInputArrowData_edge A _
  have hs := e.src_eq.symm.trans
    ((congrArg ((dgKInputInfinity A).δ 1) he).trans t.src_eq)
  have ht := e.tgt_eq.symm.trans
    ((congrArg ((dgKInputInfinity A).δ 0) he).trans t.tgt_eq)
  have hks := congrArg ((dgKInputK A).app (Opposite.op ⦋0⦌)) hs
  have hkt := congrArg ((dgKInputK A).app (Opposite.op ⦋0⦌)) ht
  have hm : (e.map (dgKInputK A)).toTruncated.edge =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow (d.square ≫ dgKInputK A)).edge :=
    congrArg ((dgKInputK A).app (Opposite.op ⦋1⦌)) he
  have hn := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport hks hkt (e.map (dgKInputK A)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow (d.square ≫ dgKInputK A)) hm
  have hn' := congrArg
    (fun m => eqToHom (congrArg HomotopyCategory.mk hks) ≫ m) hn
  simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] at hn'
  have hp := congrArg ((SpectrumHo.piFunctor 0).map) hn'
  simp only [Functor.map_comp] at hp
  exact surjective_of_iso_square _ _
    ((SpectrumHo.piFunctor 0).mapIso (eqToIso (congrArg HomotopyCategory.mk hks)))
    ((SpectrumHo.piFunctor 0).mapIso (eqToIso (congrArg HomotopyCategory.mk hkt))) hp
    ((dgKPiZeroMap_surjective_iff_kZero A _).mpr
      (dgRelativeRightArrow_kZero_surjective A d))

end SerrePositivity.KST.Fibration
