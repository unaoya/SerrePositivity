module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEdgeRepresentative
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero

/-!
概要：指定された関手同型をleft fibrationに沿って、同じ同型の類を保って持ち上げる。
方針：既存の始点固定の辺の持ち上げと可逆性の反映を関手空間に適用する。
規約：HTT 2.1.1.6、Kerodon Proposition 4.4.2.11（Tag 019K）の既存持ち上げの計算法則。
  射影の等式だけでなく、元の指定同型との一致を結論に保持する。
使われ方：R04の引き戻し間の同値を、添字同型とその逆の指定持ち上げから比較する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

private lemma exists_vertexIso_lift {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : X ⟶ Y) [LeftFibration p] (x : X _⦋0⦌) {z : Y _⦋0⦌}
    (e : VertexIso (p.app _ x) z) :
    ∃ (y : X _⦋0⦌) (hy : p.app _ y = z) (i : VertexIso x y),
      i.map p ≪≫ eqToIso (congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj Y)) hy) = e := by
  obtain ⟨b, hb⟩ := homotopyCategory_homMk_surjective (p.app _ x) z e.hom
  have hbi : IsInvertibleEdge b := by
    change IsIso (Truncated.HomotopyCategory.homMk b)
    rw [hb]
    infer_instance
  obtain ⟨F, hF₀, hFp⟩ := leftFibration_liftEdge_source p x b
  let s := SSet.yonedaEquiv F
  have hs : X.δ 1 s = x := by
    dsimp only [s]
    rw [← stdSimplex.yonedaEquiv_δ_comp, hF₀]
    exact Equiv.apply_symm_apply _ _
  let y := X.δ 0 s
  have hy : p.app _ y = z := by
    have hp : p.app (Opposite.op ⦋1⦌) s = b.edge := by
      rw [← SSet.yonedaEquiv_comp, hFp]
      exact Equiv.apply_symm_apply _ _
    dsimp only [y]
    rw [SSet.δ_naturality_apply, hp]
    exact b.tgt_eq
  let l : Truncated.Edge (X := (truncation 2).obj X) x y := ⟨s, hs, rfl⟩
  have hl : (l.map ((truncation 2).map p)).edge = b.edge := by
    change p.app (Opposite.op ⦋1⦌) s = b.edge
    rw [← SSet.yonedaEquiv_comp, hFp]
    exact Equiv.apply_symm_apply _ _
  have hli : IsInvertibleEdge l := leftFibration_reflects_invertibleEdge p l
    ((isInvertibleEdge_congr (e := l.map ((truncation 2).map p)) (f := b) hl).mpr hbi)
  let i : VertexIso x y := asIso (Truncated.HomotopyCategory.homMk l)
  refine ⟨y, hy, i, ?_⟩
  apply Iso.ext
  apply Arrow.mk_injective _ _
  simp only [Iso.trans_hom, eqToIso.hom, Arrow.arrow_mk_comp_eqToHom]
  change Arrow.mk (Truncated.HomotopyCategory.homMk (l.map ((truncation 2).map p))) =
    Arrow.mk e.hom
  rw [← hb]
  exact Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hl

/-- 関手空間の既存の辺の持ち上げは、同じ指定同型とその射影の式を保持する。 -/
@[cite HTT "2.1.1.6" (partial := special) "既存の辺の持ち上げと可逆性反映を関手空間に適用する法則。"]
lemma exists_leftFibration_functorIso_lift {A E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (f : A ⟶ E) {h : A ⟶ B} (e : FunctorIso (f ≫ p) h) :
    ∃ (g : A ⟶ E) (hg : g ≫ p = h) (i : FunctorIso f g),
      functorIsoOfEq (i.postcomp p) rfl hg = e := by
  obtain ⟨y, hy, i, hi⟩ := exists_vertexIso_lift ((ihom A).map p) (functorVertex f) e
  obtain ⟨g, hgy⟩ := (SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A E).surjective y
  subst y
  have hg : g ≫ p = h := functorVertex_injective hy
  refine ⟨g, hg, i, ?_⟩
  subst h
  apply Iso.ext
  simpa only [functorIsoOfEq, functorIso_postcomp_hom, VertexIso.map, Functor.mapIso_hom, SSet.hoFunctor, Functor.toCatHom_toFunctor, Iso.trans_hom,
    eqToIso_refl, Iso.refl_hom, Category.comp_id] using congrArg Iso.hom hi

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
