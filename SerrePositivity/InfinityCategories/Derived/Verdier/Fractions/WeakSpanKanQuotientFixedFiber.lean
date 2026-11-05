module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) (x y : B.obj _⦋0⦌)

/-- 概要：元の実全族写像の、元の両端固定 span 全体への実 fiber 制限。
方針：厳密な q 保存と元の終点計算で同じ商 fiber へ持ち上げる。
規約：底の終点は文字通り q(y)。零単体の端点表示に依存しない。
使われ方：K-B-S の元の全族写像に要求する全 fiber 比較の左辺。 -/
def weakSpanKanQuotientFamilyFixedFiber :
    fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y ⟶
      vertexFiber (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  vertexFiberLift _ _
    (fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y ≫ weakSpanKanQuotientFamilyMap h x)
    (by rw [Category.assoc, weakSpanKanQuotientFamilyMap_projection,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedFamily_projection, SSet.const_comp])

/-- 概要：同じ元の単位の零単体上の制限を、同じ商の実 fiber へ送る。
方針：元の零単体持ち上げ・実単位・指定商比較を合成する。
規約：同じ Ind-S の単位を使い、対象別に選び直さない。
使われ方：降下した全族写像の固定 fiber と比較する指定単位。 -/
def weakSpanKanQuotientZeroSimplexFixedFiber :
    fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y ⟶
      vertexFiber (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  vertexFiberLift _ _
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedZeroSimplexLift i x y ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientSimplexFamilyMap h x (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit i x)) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientSimplexFamilyMap_projection h x _
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_projection i x), ← Category.assoc]
      change (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedZeroSimplexLift i x y ≫
        pullback.snd _ _) ≫ _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedZeroSimplexLift, pullback.lift_snd, ← Category.assoc, SSet.const_comp,
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex, SSet.const_comp])

/-- 概要：元の固定 span の比較 prism を、同じ商の元の fiber 内へ送る。
方針：全時刻で底に定値な元の prism を実単位と指定商比較に合成する。
規約：全パラメータで q(y) を固定する。
使われ方：全 fiber 関手同型の元になる同じ実 prism。 -/
def weakSpanKanQuotientFixedFiberPrism :
    nerve (TransportSimplexCategory (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)) ⊗
      Δ[1] ⟶
      vertexFiber (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  vertexFiberLift _ _
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedSimplexFamilyPrism i x y ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientSimplexFamilyMap h x (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit i x)) (by
      rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientSimplexFamilyMap_projection h x _
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_projection i x), ← Category.assoc]
      change (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedSimplexFamilyPrism i x y ≫ pullback.snd _ _) ≫ _ = _
      rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedSimplexFamilyPrism, pullback.lift_snd, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedSimplexCollapse_base, SSet.const_comp])


/-- 概要：元の固定 span の単体圏で、指定相対降下が回収する制限を同じ商 fiber に読む。
方針：元の全族への単体関手と元の指定比較を合成する。
規約：元の全族の初頂点自然性で底を厳密に固定する。
使われ方：実 prism の終端と相対制限同型の共通の標的。 -/
def weakSpanKanQuotientResolutionFixedFiber :
    nerve (TransportSimplexCategory (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)) ⟶
      vertexFiber (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
        (q.hom.app (Opposite.op ⦋0⦌) y) :=
  vertexFiberLift _ _
    (nerveMap (transportSimplexFunctor (fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)) ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalSimplexMap h x (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit i x)) (by
        rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalSimplexMap_projection h x _
          (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_projection i x), ← Category.assoc,
          ← Category.assoc, transportSimplexFirstVertexMap_naturality,
          Category.assoc, Category.assoc,
          ← Category.assoc (fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)
            (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x) q.hom,
          _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedFamily_projection, SSet.const_comp, SSet.comp_const])

/-- 概要：元の固定 span の全単体上で、同じ実単位と相対降下の指定制限を比較する。
方針：元の底を全時刻固定した実 prism の両端を回収する。
規約：同じ商 fiber 内の全単体的ホモトピー。点別の比較へ弱めない。
使われ方：元の全 fiber 制限へ戻すための同じ関手同型。 -/
def weakSpanKanQuotientFixedFiberHomotopy :
    SSet.Homotopy
      (transportSimplexFirstVertexMap _ ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroSimplexFixedFiber h x y)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientResolutionFixedFiber h x y) where
  h := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberPrism h x y
  h₀ := by
    change SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberPrism h x y =
      transportSimplexFirstVertexMap _ ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroSimplexFixedFiber h x y
    apply vertexFiber_hom_ext
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberPrism,
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroSimplexFixedFiber, vertexFiberLift_ι]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedSimplexFamilyPrism_zero, Category.assoc]
  h₁ := by
    change SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberPrism h x y =
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientResolutionFixedFiber h x y
    apply vertexFiber_hom_ext
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberPrism,
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientResolutionFixedFiber, vertexFiberLift_ι]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedSimplexFamilyPrism_one, Category.assoc]
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
      (transportSimplexFirstVertexMap _ ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber h x y)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientResolutionFixedFiber h x y) := by
  let p := smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x)
  let r := transportSimplexFirstVertexMap (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamily B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x)
  let rS := transportSimplexFirstVertexMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)
  let j := fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y
  let J := nerveMap (transportSimplexFunctor j)
  let b := r ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x ≫ q.hom
  let z := q.hom.app (Opposite.op ⦋0⦌) y
  have hJ : J ≫ r = rS ≫ j := transportSimplexFirstVertexMap_naturality j
  have hb : J ≫ b = SSet.const z := by
    change J ≫ r ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x ≫ q.hom = _
    rw [← Category.assoc, ← Category.assoc, hJ, Category.assoc, Category.assoc,
      ← Category.assoc j (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x) q.hom,
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanFixedFamily_projection, SSet.const_comp, SSet.comp_const]
  let jOver : Over.mk (SSet.const z : nerve (TransportSimplexCategory
      (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)) ⟶ C.obj) ⟶ Over.mk b :=
    Over.homMk J hb
  let vL := relativeFunctorVertex p b (r ≫ weakSpanKanQuotientFamilyMap h x)
    (by dsimp only [p, b]; rw [Category.assoc, weakSpanKanQuotientFamilyMap_projection])
  let vR := relativeFunctorVertex p b
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalSimplexMap h x (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit i x))
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalSimplexMap_projection h x _
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanUnstraighteningUnit_projection i x))
  have e : VertexIso vL vR := weakSpanKanQuotientFamilyMapRestrictionIso h x
  have e' := e.map (relativeFunctorOverPre p jOver)
  have hL : (relativeFunctorOverPre p jOver).app (Opposite.op ⦋0⦌) vL =
      relativeFunctorVertex p (SSet.const z)
        ((rS ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber h x y) ≫ vertexFiberι p z)
        (by rw [Category.assoc, vertexFiberι_comp, SSet.comp_const]) := by
    dsimp only [vL]
    erw [relativeFunctorOverPre_vertex]
    apply Subtype.ext
    change functorVertex (J ≫ r ≫ weakSpanKanQuotientFamilyMap h x) = _
    apply congrArg functorVertex
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber, vertexFiberLift_ι]
    rw [← Category.assoc, hJ, Category.assoc]
    dsimp only [p, z, j]
    rw [vertexFiberLift_ι]
  have hR : (relativeFunctorOverPre p jOver).app (Opposite.op ⦋0⦌) vR =
      relativeFunctorVertex p (SSet.const z)
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientResolutionFixedFiber h x y ≫ vertexFiberι p z)
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
    FunctorIso (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber h x y)
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroSimplexFixedFiber h x y) := by
  letI := vertexFiber_kanComplex_of_leftFibration
    (smallLeftUnstraighteningProjection (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientDiagram h x))
    (q.hom.app (Opposite.op ⦋0⦌) y)
  have e := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso h x y ≪≫
    (functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberHomotopy h x y)).symm
  exact (localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_isLocalization
      (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)) _).preimageVertexIso e

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiber := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFixedFiberHomotopy := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberHomotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberPrism (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFixedFiberPrism := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberPrism

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientResolutionFixedFiber (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientResolutionFixedFiber := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientResolutionFixedFiber

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroSimplexFixedFiber (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroSimplexFixedFiber := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroSimplexFixedFiber

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiber._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiber.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiber.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_10 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_11 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_11

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_12 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_12

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_13 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_13

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_14 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_14

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_15 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_15

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_16 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_16

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_7 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_8 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_9 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFamilyFixedFiberRestrictionIso._proof_9

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFixedFiberHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFixedFiberHomotopy._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberHomotopy._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFixedFiberHomotopy._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberHomotopy._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFixedFiberPrism._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberPrism._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientFixedFiberPrism.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientFixedFiberPrism.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientResolutionFixedFiber._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientResolutionFixedFiber._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientResolutionFixedFiber.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientResolutionFixedFiber.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroSimplexFixedFiber._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroSimplexFixedFiber._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroSimplexFixedFiber._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroSimplexFixedFiber._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientZeroSimplexFixedFiber.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientZeroSimplexFixedFiber.eq_1
