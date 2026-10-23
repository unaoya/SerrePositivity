module

public import SerrePositivity.InfinityCategories.HomotopyLimits.EdgeCosliceFamilySquare
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalCosliceSource
public import SerrePositivity.InfinityCategories.F1B.IntervalComposition
public import SerrePositivity.InfinityCategories.F1B.IntervalFunctorHom
public import SerrePositivity.InfinityCategories.F1B.SquareComposition

/-!
概要：区間を被覆する coCartesian 辺による前合成は、区間写像空間のホモトピー同値。
方針：錐の比較 span を任意の族で元の前合成と照合し、両射影の同値性を移す。
規約：通常の Hom の全単射へ弱めない。使われ方：Quillen 導来随伴の単位の各点の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local instance] vertexFiber_kanComplex_of_leftFibration
variable {T E : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ E) (y : E _⦋0⦌)

/-- 元の任意の錐の族で、始点側の写像は固定辺と終点側の写像の合成である。 -/
lemma edgeCosliceIntervalMap_composition (a : T ⟶ vertexFiber (sliceUnderProjection e) y) :
    constantFunctorHomMap T (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge e)) ≫
      intervalFamilyHom (a ≫ edgeCosliceIntervalMap e y 0) =
        intervalFamilyHom (a ≫ edgeCosliceIntervalMap e y 1) := by
  let f := (edgeCosliceEdge e).map ((truncation 2).map (constantFunctorMap T E))
  let c : SSet.Truncated.Edge (X := (truncation 2).obj ((ihom T).obj E))
      (functorVertex (SSet.const (SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ e)) : T ⟶ E))
      (functorVertex (SSet.const (SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) ≫ e)) : T ⟶ E)) :=
    ⟨f.edge, f.src_eq.trans (constantFunctorMap_vertex T _),
      f.tgt_eq.trans (constantFunctorMap_vertex T _)⟩
  have hc : constantFunctorHomMap T
      (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge e)) =
        SSet.Truncated.HomotopyCategory.homMk c :=
    homMk_transport (constantFunctorMap_vertex T _) (constantFunctorMap_vertex T _) f c rfl
  have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = homotopyIntervalEdge.edge := by
    apply SSet.stdSimplex.ext
    intro j
    fin_cases j <;> rfl
  have hq := homMk_comp_eq_of_square c
    (SSet.Truncated.Edge.id (X := (truncation 2).obj ((ihom T).obj E))
      (functorVertex (SSet.const y : T ⟶ E)))
    (intervalFamilyEdge (a ≫ edgeCosliceIntervalMap e y 1))
    (intervalFamilyEdge (a ≫ edgeCosliceIntervalMap e y 0))
    (edgeCosliceFamilySquare e y a) ?_ ?_ ?_ ?_
  · rw [SSet.Truncated.HomotopyCategory.homMk_id, Category.comp_id] at hq
    rw [hc]
    exact hq
  · change (edgeCosliceFamilySquare e y a).app (Opposite.op ⦋1⦌)
      (homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₀ ≫ edgeCosliceFamilySquare e y a) = _
    rw [edgeCosliceFamilySquare_bottom, SSet.yonedaEquiv_comp]
    rfl
  · change (edgeCosliceFamilySquare e y a).app (Opposite.op ⦋1⦌)
      (homotopyIntervalEdge.edge, _) = _
    rw [← hi]
    change SSet.yonedaEquiv (SSet.ι₁ ≫ edgeCosliceFamilySquare e y a) = _
    rw [edgeCosliceFamilySquare_top]
    change PinchedHom.constant (X := (ihom T).obj E)
      (functorVertex (SSet.const y : T ⟶ E)) 1 = _
    exact pinchedConstant_one _
  · change (edgeCosliceFamilySquare e y a).app (Opposite.op ⦋1⦌)
      (_, homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (prismEndpoint 0 Δ[1] ≫ edgeCosliceFamilySquare e y a) = _
    exact congrArg SSet.yonedaEquiv (edgeCosliceFamilySquare_side e y a 0)
  · change (edgeCosliceFamilySquare e y a).app (Opposite.op ⦋1⦌)
      (_, homotopyIntervalEdge.edge) = _
    rw [← hi]
    change SSet.yonedaEquiv (prismEndpoint 1 Δ[1] ≫ edgeCosliceFamilySquare e y a) = _
    exact congrArg SSet.yonedaEquiv (edgeCosliceFamilySquare_side e y a 1)

/-- 二つの制限を結ぶ比較 span は、元の区間模型の前合成をホモトピーで表す。 -/
lemma edgeCosliceIntervalMap_precompose [Quasicategory E] :
    Nonempty (SSet.Homotopy
      (edgeCosliceIntervalMap e y 0 ≫ intervalPrecompose y
        (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge e)))
      (edgeCosliceIntervalMap e y 1)) := by
  apply intervalFamilyHom_eq_imp_homotopy
  rw [intervalPrecompose_family]
  simpa only [Category.id_comp] using edgeCosliceIntervalMap_composition e y
    (𝟙 (vertexFiber (sliceUnderProjection e) y))

/-- 指定端点への錐の制限が trivial Kan なら、区間模型への比較も同値である。 -/
lemma edgeCosliceIntervalMap_isQCatEquivalence [Quasicategory E] (j : Fin 2)
    [TrivialKanFibration (cosliceRestrictionFiberMap e (stdSimplex.δ j) y)] :
    IsQCatEquivalence (edgeCosliceIntervalMap e y j) := by
  exact (isQCatEquivalence_of_trivialKanFibration
    (cosliceRestrictionFiberMap e (stdSimplex.δ j) y)).comp
    ((qCatEquivalenceOfIso (cosliceFiberDiagramIso
      (Equiv.symm_apply_apply SSet.yonedaEquiv (stdSimplex.δ j ≫ e)).symm y)).isQCatEquivalence.comp
      (cosliceFiberToIntervalMappingSpace_isQCatEquivalence _ y))

/-- 終点側への区間写像空間比較は、任意の元の固定辺に対して同値である。 -/
lemma edgeCosliceIntervalMap_target_isQCatEquivalence [Quasicategory E] :
    IsQCatEquivalence (edgeCosliceIntervalMap e y 0) := by
  have := cosliceTriangleTarget_trivialKanFibration e y
  exact edgeCosliceIntervalMap_isQCatEquivalence e y 0

/-- 元の固定辺が coCartesian なら、始点側への区間写像空間比較は同値である。 -/
lemma edgeCosliceIntervalMap_source_isQCatEquivalence [Quasicategory E]
    (p : E ⟶ (Δ[1] : SSet.{u})) (hp : e ≫ p = 𝟙 Δ[1])
    (he : IsCocartesianEdge p (SSet.yonedaEquiv e))
    (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :
    IsQCatEquivalence (edgeCosliceIntervalMap e y 1) := by
  have := cosliceTriangleSource_trivialKanFibration p e hp he y hy
  exact edgeCosliceIntervalMap_isQCatEquivalence e y 1

/-- 元の coCartesian 辺による前合成は、上段終域への区間写像空間のホモトピー同値。 -/
lemma intervalPrecompose_isSimplicialHomotopyEquivalence_of_cocartesian
    [Quasicategory E] (p : E ⟶ (Δ[1] : SSet.{u})) (hp : e ≫ p = 𝟙 Δ[1])
    (he : IsCocartesianEdge p (SSet.yonedaEquiv e))
    (hy : p.app (Opposite.op ⦋0⦌) y = stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :
    IsSimplicialHomotopyEquivalence (intervalPrecompose y
      (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge e))) := by
  obtain ⟨H⟩ := edgeCosliceIntervalMap_precompose e y
  have ht := edgeCosliceIntervalMap_target_isQCatEquivalence e y
  have hs := edgeCosliceIntervalMap_source_isQCatEquivalence e y p hp he hy
  have hcomp := hs.ofFunctorIso (functorIsoOfSimplicialHomotopy H).symm
  exact (ht.cancel_left hcomp).isSimplicialHomotopyEquivalence

end
end SerrePositivity.InfinityCategories.HomotopyLimits
