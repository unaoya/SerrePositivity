module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanFixedSimplexCollapse
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorConstFiber

/-!
概要：元の実全族写像と同じ単体圏単位を、固定した商 fiber 内で比較する。
方針：元の固定 span の全単体比較 prism を、同じ商の実 fiber へ持ち上げる。
規約：元の q・全族写像・単位を固定し、追加の存在仮定を導入しない。
使われ方：K-B-S の全 fiber 単位回収と既存指定恒等点への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌)

/-- 概要：元の実全族写像の、元の両端固定 span 全体への実 fiber 制限。
方針：厳密な q 保存と元の終点計算で同じ商 fiber へ持ち上げる。
規約：底の終点は文字通り q(y)。零単体の端点表示に依存しない。
使われ方：K-B-S の元の全族写像に要求する全 fiber 比較の左辺。 -/
def weakSpanKanQuotientFamilyFixedFiber :
    fixedMarkedSpans B.obj (weakEquivalences i) x y ⟶
      vertexFiber (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  vertexFiberLift _ _
    (fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y ≫ weakSpanKanQuotientFamilyMap h x)
    (by rw [Category.assoc, weakSpanKanQuotientFamilyMap_projection,
      ← Category.assoc, weakSpanFixedFamily_projection, SSet.const_comp])

/-- 概要：同じ元の単位の零単体上の制限を、同じ商の実 fiber へ送る。
方針：元の零単体持ち上げ・実単位・指定商比較を合成する。
規約：同じ Ind-S の単位を使い、対象別に選び直さない。
使われ方：降下した全族写像の固定 fiber と比較する指定単位。 -/
def weakSpanKanQuotientZeroSimplexFixedFiber :
    fixedMarkedSpans B.obj (weakEquivalences i) x y ⟶
      vertexFiber (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  vertexFiberLift _ _
    (weakSpanFixedZeroSimplexLift i x y ≫
      weakSpanKanQuotientSimplexFamilyMap h x (weakSpanKanUnstraighteningUnit i x)) (by
      rw [Category.assoc, weakSpanKanQuotientSimplexFamilyMap_projection h x _
        (weakSpanKanUnstraighteningUnit_projection i x), ← Category.assoc]
      change (weakSpanFixedZeroSimplexLift i x y ≫
        pullback.snd _ _) ≫ _ = _
      rw [weakSpanFixedZeroSimplexLift, pullback.lift_snd, ← Category.assoc, SSet.const_comp,
        transportSimplexFirstVertexMap_zeroIndex, SSet.const_comp])

/-- 概要：元の固定 span の比較 prism を、同じ商の元の fiber 内へ送る。
方針：全時刻で底に定値な元の prism を実単位と指定商比較に合成する。
規約：全パラメータで q(y) を固定する。
使われ方：全 fiber 関手同型の元になる同じ実 prism。 -/
def weakSpanKanQuotientFixedFiberPrism :
    nerve (TransportSimplexCategory (fixedMarkedSpans B.obj (weakEquivalences i) x y)) ⊗
      Δ[1] ⟶
      vertexFiber (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  vertexFiberLift _ _
    (weakSpanFixedSimplexFamilyPrism i x y ≫
      weakSpanKanQuotientSimplexFamilyMap h x (weakSpanKanUnstraighteningUnit i x)) (by
      rw [Category.assoc, weakSpanKanQuotientSimplexFamilyMap_projection h x _
        (weakSpanKanUnstraighteningUnit_projection i x), ← Category.assoc]
      change (weakSpanFixedSimplexFamilyPrism i x y ≫ pullback.snd _ _) ≫ _ = _
      rw [weakSpanFixedSimplexFamilyPrism, pullback.lift_snd, ← Category.assoc,
        weakSpanFixedSimplexCollapse_base, SSet.const_comp])


/-- 概要：元の固定 span の単体圏で、指定相対降下が回収する制限を同じ商 fiber に読む。
方針：元の全族への単体関手と元の指定比較を合成する。
規約：元の全族の初頂点自然性で底を厳密に固定する。
使われ方：実 prism の終端と相対制限同型の共通の標的。 -/
def weakSpanKanQuotientResolutionFixedFiber :
    nerve (TransportSimplexCategory (fixedMarkedSpans B.obj (weakEquivalences i) x y)) ⟶
      vertexFiber (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  vertexFiberLift _ _
    (nerveMap (transportSimplexFunctor (fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y)) ≫
      weakSpanKanQuotientTotalSimplexMap h x (weakSpanKanUnstraighteningUnit i x)) (by
        rw [Category.assoc, weakSpanKanQuotientTotalSimplexMap_projection h x _
          (weakSpanKanUnstraighteningUnit_projection i x), ← Category.assoc,
          ← Category.assoc, transportSimplexFirstVertexMap_naturality,
          Category.assoc, Category.assoc,
          ← Category.assoc (fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y)
            (markedSpanFamilyProjection B.obj (weakEquivalences i) x) q.hom,
          weakSpanFixedFamily_projection, SSet.const_comp, SSet.comp_const])

/-- 概要：元の固定 span の全単体上で、同じ実単位と相対降下の指定制限を比較する。
方針：元の底を全時刻固定した実 prism の両端を回収する。
規約：同じ商 fiber 内の全単体的ホモトピー。点別の比較へ弱めない。
使われ方：元の全 fiber 制限へ戻すための同じ関手同型。 -/
def weakSpanKanQuotientFixedFiberHomotopy :
    SSet.Homotopy
      (transportSimplexFirstVertexMap _ ≫ weakSpanKanQuotientZeroSimplexFixedFiber h x y)
      (weakSpanKanQuotientResolutionFixedFiber h x y) where
  h := weakSpanKanQuotientFixedFiberPrism h x y
  h₀ := by
    change SSet.ι₀ ≫ weakSpanKanQuotientFixedFiberPrism h x y =
      transportSimplexFirstVertexMap _ ≫ weakSpanKanQuotientZeroSimplexFixedFiber h x y
    apply vertexFiber_hom_ext
    simp only [Category.assoc, weakSpanKanQuotientFixedFiberPrism,
      weakSpanKanQuotientZeroSimplexFixedFiber, vertexFiberLift_ι]
    rw [← Category.assoc, weakSpanFixedSimplexFamilyPrism_zero, Category.assoc]
  h₁ := by
    change SSet.ι₁ ≫ weakSpanKanQuotientFixedFiberPrism h x y =
      weakSpanKanQuotientResolutionFixedFiber h x y
    apply vertexFiber_hom_ext
    simp only [Category.assoc, weakSpanKanQuotientFixedFiberPrism,
      weakSpanKanQuotientResolutionFixedFiber, vertexFiberLift_ι]
    rw [← Category.assoc, weakSpanFixedSimplexFamilyPrism_one, Category.assoc]
    rfl
  rel := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property


/-- 概要：元の実全族の固定 fiber 制限は、同じ単体圏の指定制限を fiber 内で回収する。
方針：同じ相対降下同型を元の固定 span の単体関手で制限し、同じ定値 fiber へ読む。
規約：底を忘れた全空間内の同型では代用しない。
使われ方：元の全 fiber に同じ実単位を戻す比較。 -/
def weakSpanKanQuotientFamilyFixedFiberRestrictionIso :
    FunctorIso
      (transportSimplexFirstVertexMap _ ≫ weakSpanKanQuotientFamilyFixedFiber h x y)
      (weakSpanKanQuotientResolutionFixedFiber h x y) := by
  let p := smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)
  let r := transportSimplexFirstVertexMap (markedSpanFamily B.obj (weakEquivalences i) x)
  let rS := transportSimplexFirstVertexMap (fixedMarkedSpans B.obj (weakEquivalences i) x y)
  let j := fixedMarkedSpanToFamily B.obj (weakEquivalences i) x y
  let J := nerveMap (transportSimplexFunctor j)
  let b := r ≫ markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom
  let z := q.hom.app (Opposite.op ⦋0⦌) y
  have hJ : J ≫ r = rS ≫ j := transportSimplexFirstVertexMap_naturality j
  have hb : J ≫ b = SSet.const z := by
    change J ≫ r ≫ markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom = _
    rw [← Category.assoc, ← Category.assoc, hJ, Category.assoc, Category.assoc,
      ← Category.assoc j (markedSpanFamilyProjection B.obj (weakEquivalences i) x) q.hom,
      weakSpanFixedFamily_projection, SSet.const_comp, SSet.comp_const]
  let jOver : Over.mk (SSet.const z : nerve (TransportSimplexCategory
      (fixedMarkedSpans B.obj (weakEquivalences i) x y)) ⟶ C.obj) ⟶ Over.mk b :=
    Over.homMk J hb
  let vL := relativeFunctorVertex p b (r ≫ weakSpanKanQuotientFamilyMap h x)
    (by dsimp only [p, b]; rw [Category.assoc, weakSpanKanQuotientFamilyMap_projection])
  let vR := relativeFunctorVertex p b
    (weakSpanKanQuotientTotalSimplexMap h x (weakSpanKanUnstraighteningUnit i x))
    (weakSpanKanQuotientTotalSimplexMap_projection h x _
      (weakSpanKanUnstraighteningUnit_projection i x))
  have e : VertexIso vL vR := weakSpanKanQuotientFamilyMapRestrictionIso h x
  have e' := e.map (relativeFunctorOverPre p jOver)
  have hL : (relativeFunctorOverPre p jOver).app (Opposite.op ⦋0⦌) vL =
      relativeFunctorVertex p (SSet.const z)
        ((rS ≫ weakSpanKanQuotientFamilyFixedFiber h x y) ≫ vertexFiberι p z)
        (by rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]) := by
    dsimp only [vL]
    erw [relativeFunctorOverPre_vertex]
    apply Subtype.ext
    change functorVertex (J ≫ r ≫ weakSpanKanQuotientFamilyMap h x) = _
    apply congrArg functorVertex
    simp only [Category.assoc, weakSpanKanQuotientFamilyFixedFiber, vertexFiberLift_ι]
    rw [← Category.assoc, hJ, Category.assoc]
    dsimp only [p, z, j]
    rw [vertexFiberLift_ι]
  have hR : (relativeFunctorOverPre p jOver).app (Opposite.op ⦋0⦌) vR =
      relativeFunctorVertex p (SSet.const z)
        (weakSpanKanQuotientResolutionFixedFiber h x y ≫ vertexFiberι p z)
        (by rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]) := by
    dsimp only [vR]
    erw [relativeFunctorOverPre_vertex]
    apply Subtype.ext
    apply congrArg functorVertex
    exact (vertexFiberLift_ι _ _ _ _).symm
  erw [hL, hR] at e'
  have e'' := e'.map (relativeFunctorConstFiberHom p z)
  erw [relativeFunctorConstFiberHom_vertex, relativeFunctorConstFiberHom_vertex] at e''
  exact e''

/-- 概要：元の実全族写像の全固定 fiber は、同じ実単位の零単体制限と関手同型。
方針：同じ fiber 内の相対制限同型と実 prism を合成し、元の初頂点局所化で反映する。
規約：元の全 fiber を一度に回収し、各点別の比較に弱めない。
使われ方：K-B-S の元の Kan 単位と既存指定恒等点への正規化。 -/
def weakSpanKanQuotientFamilyFixedFiberIso :
    FunctorIso (weakSpanKanQuotientFamilyFixedFiber h x y)
      (weakSpanKanQuotientZeroSimplexFixedFiber h x y) := by
  letI := vertexFiber_kanComplex_of_leftFibration
    (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
    (q.hom.app (Opposite.op ⦋0⦌) y)
  have e := weakSpanKanQuotientFamilyFixedFiberRestrictionIso h x y ≪≫
    (functorIsoOfSimplicialHomotopy (weakSpanKanQuotientFixedFiberHomotopy h x y)).symm
  exact (localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_isLocalization
      (fixedMarkedSpans B.obj (weakEquivalences i) x y)) _).preimageVertexIso e

end SerrePositivity.KST.Fibration
