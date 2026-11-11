module
public import SerrePositivity.KST.SConstruction.KCompositionPrismFaces
public import SerrePositivity.KST.SConstruction.KPrismCutSpanFamilies
public import SerrePositivity.KST.SConstruction.CoherentTriangleTraceRecovery

/-! # 元の K 合成二単体の同じ suspension Hom に値を取る三正方形
概要：元の合成 prism の両端を元の K の段へ同定し、三つの実正方形と共有区間を回収する。
方針：元の固定構造射の頂点の式で両端を照合し、一般の Hom 正方形を適用する。
規約：零段も元の K のままで、写像空間や正方形を選び直さない。
使われ方：元の入力の合成面の実比較を既存の BF 厳密化へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.CoherentPathCoordinates SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kCompositionPrismSquaresPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の prism の各下端頂点は、元の段の suspension そのもの。 -/
lemma kKanOriginalPrism_bottom_object {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌)
    (a : (Δ[n] : SSet.{u + 1}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject ((kKanOriginalSuspensionPrism r F s).app (Opposite.op ⦋0⦌)
      (a, SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj (s.obj (a 0)))).level r).space := by
  have h := congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject
      (q.app (Opposite.op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (kKanOriginalSuspensionPrism_vertex r F s a)
  have he : (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((kKanSequence (F.obj (s.obj (a 0)))).sigma r)).edge).app
      (Opposite.op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj (s.obj (a 0)))).level r).space) := by
    have ht : SSet.stdSimplex.objEquiv
        (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2) :
          (Δ[1] : SSet.{u + 1}) _⦋0⦌) = SimplexCategory.δ (1 : Fin 2) := by
      ext t
      fin_cases t
      rfl
    rw [SSet.yonedaEquiv_symm_app, ht]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((kKanSequence (F.obj (s.obj (a 0)))).sigma r)).src_eq
  have hc : (SSet.const a : (Δ[1] : SSet.{u + 1}) ⟶ Δ[n]).app
      (Opposite.op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = a := by
    simp only [SSet.const_app, SimplexCategory.const_eq_id, op_id,
      CategoryTheory.Functor.map_id_apply]
    rfl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject ((kKanOriginalSuspensionPrism r F s).app _
    ((SSet.const a).app _ (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)),
      SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2))) = _ at h
  rw [hc] at h
  exact h.trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject he)

variable {I : Type u} [SmallCategory I] (r : ℕ) (F : I ⥤ StableModel.{u})
  {x y z : I} (f : x ⟶ y) (g : y ⟶ z)

/-- 元の合成 prism の共通始点は、元の始域の段の suspension。 -/
lemma kKanOriginalCompositionPrism_source :
    trianglePrismSource (kKanOriginalCompositionPrism r F f g) =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space :=
  kKanOriginalPrism_bottom_object r F (ComposableArrows.mk₂ f g) (stdSimplex.obj₀Equiv.symm 0)

/-- 元の合成 prism の共通終点は、元の終域の次段。 -/
lemma kKanOriginalCompositionPrism_target :
    trianglePrismTarget (kKanOriginalCompositionPrism r F f g) =
      ((kKanSequence (F.obj z)).level (r + 1)).space :=
  kKanOriginalPrism_top_object r F (ComposableArrows.mk₂ f g) (stdSimplex.obj₀Equiv.symm 2)

/-- 元の合成 prism の共通 Hom は、元の指定 suspension 写像空間である。 -/
lemma kKanOriginalCompositionPrism_hom :
    SimplicialCategory.sHom (trianglePrismSource (kKanOriginalCompositionPrism r F f g))
      (trianglePrismTarget (kKanOriginalCompositionPrism r F f g)) =
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
        ((kKanSequence (F.obj z)).level (r + 1)).space).right := by
  rw [kKanOriginalCompositionPrism_source, kKanOriginalCompositionPrism_target]
  rfl

/-- 元の合成二単体 prism の三つの正方形を、同じ元の suspension Hom に表示する。 -/
def kKanOriginalCompositionMappingSquare (q : Fin 3) : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension ((kKanSequence (F.obj x)).level r).space)
      ((kKanSequence (F.obj z)).level (r + 1)).space).right :=
  trianglePrismMappingSquare (kKanOriginalCompositionPrism r F f g) q ≫
    eqToHom (kKanOriginalCompositionPrism_hom r F f g)

/-- 最初と中央の正方形は、同じ元の suspension Hom 内の共有区間で貼り合う。 -/
lemma kKanOriginalCompositionMappingSquare_shared_first :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        kKanOriginalCompositionMappingSquare r F f g 0 =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        kKanOriginalCompositionMappingSquare r F f g 1 := by
  simpa only [kKanOriginalCompositionMappingSquare, Category.assoc] using
    congrArg (fun q => q ≫ eqToHom (kKanOriginalCompositionPrism_hom r F f g))
      (trianglePrismMappingSquare_shared_first (kKanOriginalCompositionPrism r F f g))

/-- 中央と最後の正方形も、同じ元の suspension Hom 内の共有区間で貼り合う。 -/
lemma kKanOriginalCompositionMappingSquare_shared_second :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        kKanOriginalCompositionMappingSquare r F f g 1 =
      lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
        kKanOriginalCompositionMappingSquare r F f g 2 := by
  simpa only [kKanOriginalCompositionMappingSquare, Category.assoc] using
    congrArg (fun q => q ≫ eqToHom (kKanOriginalCompositionPrism_hom r F f g))
      (trianglePrismMappingSquare_shared_second (kKanOriginalCompositionPrism r F f g))

/-- 最初の正方形の外側区間は、元の合成射の上側三角形の同じ復号辺。 -/
lemma kKanOriginalCompositionMappingSquare_composite_upper :
    lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫
      kKanOriginalCompositionMappingSquare r F f g 0 =
      SSet.yonedaEquiv.symm
        (coherentSquareMappingLeftTop (kKanSuspensionMappingTriangles r F (f ≫ g))).edge := by
  rw [kKanOriginalCompositionMappingSquare, ← Category.assoc,
    trianglePrismMappingSquare_skip_second, Category.assoc, eqToHom_trans]
  exact coherentTriangleTrace_specified_face _ _ _
    (kKanSuspensionMappingTriangles r F (f ≫ g)).leftTop
    (kKanOriginalCompositionImage_composite_upper r F f g) _

/-- 最後の正方形の外側区間は、元の合成射の下側三角形の同じ復号辺。 -/
lemma kKanOriginalCompositionMappingSquare_composite_lower :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
      kKanOriginalCompositionMappingSquare r F f g 2 =
      SSet.yonedaEquiv.symm
        (coherentSquareMappingBottomRight (kKanSuspensionMappingTriangles r F (f ≫ g))).edge := by
  rw [kKanOriginalCompositionMappingSquare, ← Category.assoc,
    trianglePrismMappingSquare_skip_first, Category.assoc, eqToHom_trans]
  exact coherentTriangleTrace_specified_face _ _ _
    (kKanSuspensionMappingTriangles r F (f ≫ g)).bottomRight
    (kKanOriginalCompositionImage_composite_lower r F f g) _

end SerrePositivity.KST.SConstruction
