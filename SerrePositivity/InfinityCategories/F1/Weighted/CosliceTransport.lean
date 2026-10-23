module

public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationPrismTransport
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveTransportPrism
public import SerrePositivity.InfinityCategories.F1.Universe.Prism
public import SerrePositivity.InfinityCategories.F1.Coherent.EdgeEquiv
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConstantSimplex
public import SerrePositivity.InfinityCategories.Coherent.Quasicategory

/-!
概要：左 coslice の fiber 比較を介して、反転した豊穣係数の射と実際の transport を比較する。
方針：weighted nerve の係数輸送の prism を宇宙持ち上げし、coherent な coslice 比較へ合成する。
規約：F2 の比較射をそのまま使い、極限や余極限を主張しない。
使われ方：Kerodon Proposition 5.2.2.8、Corollary 5.6.0.6、左 fiber の具体的な比較の射への自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：strict 図式の射は、その係数の射を表す coherent な辺になる。
方針：coherent な一単体を端点付き射データに戻して比較する。
規約：対象の宇宙と Hom の宇宙が異なっていてよい。
使われ方：Kerodon Remark 3.1.6.3、Corollary 5.6.0.6、transport の底の辺の同定。 -/
lemma strictCoherentDiagram_edge {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) {i j : I} (f : i ⟶ j) :
    (HomotopyLimits.strictCoherentDiagram F).app (Opposite.op ⦋1⦌)
      (ULift.up (nerve.edgeMk f).edge) = (coherentNerveEdge (F.map f)).edge := by
  apply (coherentNerveArrowDataEquiv C).injective
  change coherentNerveArrowData _ = coherentNerveArrowData _
  rw [coherentNerveEdge_edge, coherentNerveArrowData_of_arrow]
  change (⟨F.obj i, F.obj j, (SimplicialCategory.homEquiv' _ _).symm
    (PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map f)) 0)⟩ :
      Σ X Y : C, X ⟶ Y) = _
  rw [pinchedConstant_zero, Equiv.symm_apply_apply]

/-- 概要：左 coslice の標準 fiber 比較の包含は weighted nerve の定値係数の比較に一致する。
方針：定値係数の fiber 持ち上げの計算則と既存の比較射の同定を使う。
規約：対象の宇宙への持ち上げを含む射の等式。
使われ方：Kerodon §4.6.7、Corollary 5.6.0.6、比較 prism の両端点の同定。 -/
lemma coherentCosliceFiberComparison_weighted_ι {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) (i : I) :
    HomotopyLimits.coherentCosliceFiberComparison x (F.obj i) ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
        (coherentNerveVertex (F.obj i)) =
    (SSet.uliftFunctor.{v, u}).map
      (weightedNerveConstantLift (HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) i) ≫
      HomotopyLimits.weightedCosliceComparison F x := by
  rw [← HomotopyLimits.weightedConstantCosliceFiberMap_eq F x i,
    HomotopyLimits.weightedConstantCosliceFiberMap, vertexFiberLift_ι]
  rfl

/-- 概要：反転した豊穣係数の射を左 coslice の全空間の prism にする。
方針：係数輸送の weighted nerve の prism を持ち上げ、既存の coslice 比較へ続ける。
規約：パラメーターは始点の反転した豊穣 Hom の宇宙持ち上げ。
使われ方：Kerodon Corollary 5.6.0.6、fiber の比較を介した射への自然性の証人。 -/
noncomputable def weightedCosliceTransportPrism {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) {i j : I} (f : i ⟶ j) :
    (Δ[1] : SSet.{max u v}) ⊗
      (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x (F.obj i)).op ⟶
      sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex x)) :=
  uliftSimplexPrism.{u, v}
    (weightedNerveTransportPrism (HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) f) ≫
    HomotopyLimits.weightedCosliceComparison F x

/-- 概要：coslice の係数輸送 prism の始点は標準 fiber 比較の包含。
方針：prism の持ち上げの始点と weighted nerve の定値係数を計算する。
規約：比較射は既存の coherentCosliceFiberComparison。
使われ方：Kerodon Corollary 5.6.0.6、transport と比較する prism の初期値。 -/
lemma weightedCosliceTransportPrism_zero {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) {i j : I} (f : i ⟶ j) :
    prismEndpoint 0 _ ≫ weightedCosliceTransportPrism F x f =
      HomotopyLimits.coherentCosliceFiberComparison x (F.obj i) ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
          (coherentNerveVertex (F.obj i)) := by
  rw [weightedCosliceTransportPrism, ← Category.assoc]
  change (simplexPrismVertex 1 0 _ ≫ uliftSimplexPrism.{u, v}
    (weightedNerveTransportPrism (HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) f)) ≫
    HomotopyLimits.weightedCosliceComparison F x = _
  rw [uliftSimplexPrism_vertex]
  change (SSet.uliftFunctor.{v, u}).map (prismEndpoint 0 _ ≫
    weightedNerveTransportPrism (HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) f) ≫
    HomotopyLimits.weightedCosliceComparison F x = _
  rw [weightedNerveTransportPrism_zero]
  exact (coherentCosliceFiberComparison_weighted_ι F x i).symm

/-- 概要：coslice の係数輸送 prism の終点は係数の射と標準 fiber 比較の合成。
方針：weighted nerve の終点の計算と持ち上げの関手性を使う。
規約：係数の射も反転して持ち上げる。
使われ方：Kerodon Corollary 5.6.0.6、元の係数の作用と実際の transport を結ぶ終点。 -/
lemma weightedCosliceTransportPrism_one {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) {i j : I} (f : i ⟶ j) :
    prismEndpoint 1 _ ≫ weightedCosliceTransportPrism F x f =
      (SSet.uliftFunctor.{v, u}).map
        ((HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map f) ≫
      HomotopyLimits.coherentCosliceFiberComparison x (F.obj j) ≫
        vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
          (coherentNerveVertex (F.obj j)) := by
  rw [weightedCosliceTransportPrism, ← Category.assoc]
  change (simplexPrismVertex 1 1 _ ≫ uliftSimplexPrism.{u, v}
    (weightedNerveTransportPrism (HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) f)) ≫
    HomotopyLimits.weightedCosliceComparison F x = _
  rw [uliftSimplexPrism_vertex]
  change (SSet.uliftFunctor.{v, u}).map (prismEndpoint 1 _ ≫
    weightedNerveTransportPrism (HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor) f) ≫
    HomotopyLimits.weightedCosliceComparison F x = _
  rw [weightedNerveTransportPrism_one, Functor.map_comp, Category.assoc,
    ← coherentCosliceFiberComparison_weighted_ι F x j]

/-- 概要：coslice の係数輸送 prism は係数の射を表す coherent な辺を被覆する。
方針：weighted nerve の底の式を持ち上げ、strict 図式の辺を計算する。
規約：始域の係数の値は底では忘れる。
使われ方：Kerodon Corollary 5.6.0.6、実際の fiber transport と比較する底の条件。 -/
lemma weightedCosliceTransportPrism_projection {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (x : C) {i j : I} (f : i ⟶ j) :
    weightedCosliceTransportPrism F x f ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)) =
    fst (Δ[1] : SSet.{max u v})
      ((SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom x (F.obj i)).op) ≫
      SSet.yonedaEquiv.symm (coherentNerveEdge (F.map f)).edge := by
  rw [weightedCosliceTransportPrism, Category.assoc,
    HomotopyLimits.weightedCosliceComparison_over, ← Category.assoc,
    uliftSimplexPrism_post, weightedNerveTransportPrism_projection]
  have he := uliftSimplexPrism_edgeFamily.{u, v}
    (A := (SimplicialCategory.sHom x (F.obj i)).op) (nerve.edgeMk f)
  erw [he]
  rw [Category.assoc, SSet.yonedaEquiv_symm_comp]
  erw [strictCoherentDiagram_edge F f]

/-- 概要：左 coslice の標準 fiber 比較は係数の射と実際の fiber transport を関手同型で結ぶ。
方針：weighted nerve からの prism の両端点と底の計算を、left fibration の prism 比較へ適用する。
規約：比較は始点の反転した豊穣 Hom から終点 fiber への二つの射の間で取る。
使われ方：Kerodon Proposition 5.2.2.8、Corollary 5.6.0.6、左 fiber の射への自然性。 -/
noncomputable def coherentCosliceFiberComparison_transportIso
    {I : Type u} [Category.{u} I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    [Quasicategory (SimplicialNerve C)] (F : I ⥤ C) (x : C) {i j : I} (f : i ⟶ j) :
    FunctorIso
      ((SSet.uliftFunctor.{v, u}).map
          ((HomotopyLimits.simplicialHomDiagram F x ⋙ SSet.opFunctor).map f) ≫
        HomotopyLimits.coherentCosliceFiberComparison x (F.obj j))
      (HomotopyLimits.coherentCosliceFiberComparison x (F.obj i) ≫
        edgeTransport (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex x)))
          (coherentNerveEdge (F.map f))) := by
  apply leftFibrationPrism_transportIso _ (coherentNerveEdge (F.map f))
    (HomotopyLimits.coherentCosliceFiberComparison x (F.obj i)) _
    (weightedCosliceTransportPrism F x f) (weightedCosliceTransportPrism_zero F x f)
    ?_ (weightedCosliceTransportPrism_projection F x f)
  rw [Category.assoc]
  exact weightedCosliceTransportPrism_one F x f

end SerrePositivity.InfinityCategories
