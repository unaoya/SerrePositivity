module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanQuotientUnstraighteningMap
public import SerrePositivity.KST.Fibration.SmallUnstraighteningIsoHom
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingFiberTransport

/-!
概要：同じ商降下比較の全空間射が、元の pointed-space 成分と全 fiber 作用を保つことを照合する。
方針：既存の小さい底変換の自然性と、指定変換の全 fiber transport 比較を合成する。
規約：元の marked span 全族への降下や全族単位の存在は主張しない。
使われ方：K-B-S の同じ全 fiber 単位・指定恒等点との照合の準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 概要：同じ商上の全空間射の pointed-space 成分は、指定降下同型の実作用そのもの。
方針：小さい底変換の縮小自然性と元の pointed-space 射影式を合成する。
規約：全空間上の厳密な等式。各 fiber の点だけの比較に弱めない。
使われ方：K-B-S の全 fiber と指定恒等点の照合に使う同じ実射。 -/
theorem weakSpanKanQuotientSimplexUnstraighteningMap_pointed :
    (SSet.uliftFunctor.{u + 1, u}).map
        (weakSpanKanQuotientSimplexUnstraighteningMap h x) ≫
      (smallLeftUnstraighteningIso (weakSpanKanQuotientDiagram h x)).hom ≫
        pullback.fst pointedSpaceProjection (weakSpanKanQuotientDiagram h x) =
    (SSet.uliftFunctor.{u + 1, u}).map
        (smallUnstraighteningFunctorHom (weakSpanKanQuotientDiagram_simplexIso h x).symm.hom) ≫
      (smallLeftUnstraighteningIso
        ((SSet.uliftFunctor.{u + 1, u}).map
          (transportSimplexFirstVertexMap B.obj ≫ q.hom) ≫ weakSpanKanQuotientDiagram h x)).hom ≫
        pullback.fst pointedSpaceProjection
          ((SSet.uliftFunctor.{u + 1, u}).map
            (transportSimplexFirstVertexMap B.obj ≫ q.hom) ≫ weakSpanKanQuotientDiagram h x) := by
  let Q := weakSpanKanQuotientDiagram h x
  let α := transportSimplexFirstVertexMap B.obj ≫ q.hom
  let P := (SSet.uliftFunctor.{u + 1, u}).map α ≫ Q
  have hb := congrArg (fun f => f ≫ pullback.fst pointedSpaceProjection Q)
    (smallLeftUnstraighteningMap_naturality P Q α rfl)
  simp only [Category.assoc, leftUnstraighteningMap_pointed] at hb
  have he := congrArg (fun f => (SSet.uliftFunctor.{u + 1, u}).map
    (smallUnstraighteningFunctorHom (weakSpanKanQuotientDiagram_simplexIso h x).symm.hom) ≫ f) hb
  simpa only [weakSpanKanQuotientSimplexUnstraighteningMap,
    CategoryTheory.Functor.map_comp, Category.assoc] using he

/-- 概要：指定降下同型による同じ実比較の全 fiber 作用は、同じ代表パラメータの transport。
方針：F1 の全 fiber transport 比較を、小さい fiber の同型で移す。
規約：元の二胞体からの同じ比較射を使い、任意の fiber 同値へ選び直さない。
使われ方：Ind-S (5) の単位を同じ商 fiber の全単体へ送る際の指定作用。 -/
def weakSpanKanQuotientSimplexComparisonFiberTransportIso
    (c : TransportSimplexCategory B.obj) :
    let F := weakSpanKanCoherentDiagram i x
    let G := (SSet.uliftFunctor.{u + 1, u}).map
      (transportSimplexFirstVertexMap B.obj ≫ q.hom) ≫ weakSpanKanQuotientDiagram h x
    let a := (weakSpanKanQuotientDiagram_simplexIso h x).symm.hom
    let b := nerveVertex c
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map
        (vertexFiberMap (smallLeftUnstraighteningProjection F)
          (smallLeftUnstraighteningProjection G) (smallUnstraighteningFunctorHom a)
          (smallUnstraighteningFunctorHom_projection a) b) ≫
        (smallLeftUnstraighteningFiberIso G b).hom ≫
          (leftUnstraighteningFiberIso G (ULift.up b)).hom)
      ((smallLeftUnstraighteningFiberIso F b).hom ≫
        (leftUnstraighteningFiberIso F (ULift.up b)).hom ≫
          edgeTransport pointedSpaceProjection
            (functorEdgeAt (intervalMappingEdgeOfVertex (smallUnstraighteningHomParameter a))
              (ULift.up b))) := by
  let F := weakSpanKanCoherentDiagram i x
  let G := (SSet.uliftFunctor.{u + 1, u}).map
    (transportSimplexFirstVertexMap B.obj ≫ q.hom) ≫ weakSpanKanQuotientDiagram h x
  let a := (weakSpanKanQuotientDiagram_simplexIso h x).symm.hom
  let b := nerveVertex c
  have ht := (leftUnstraighteningMappingVertex_pointedFiberTransportIso F G
    (smallUnstraighteningHomParameter a) (ULift.up b)).precomp
      ((smallLeftUnstraighteningFiberIso F b).hom ≫
        (leftUnstraighteningFiberIso F (ULift.up b)).hom)
  simp only [leftUnstraighteningPointedFiberMap, Category.assoc, Iso.hom_inv_id_assoc] at ht
  have hn := congrArg (fun f => f ≫ (leftUnstraighteningFiberIso G (ULift.up b)).hom)
    (smallLeftUnstraighteningOverMap_fiber_naturality F G (unstraighteningFunctorHom a)
      (unstraighteningFunctorHom_projection a) b)
  have hn' : (SSet.uliftFunctor.{u + 1, u}).map
      (vertexFiberMap (smallLeftUnstraighteningProjection F)
        (smallLeftUnstraighteningProjection G) (smallUnstraighteningFunctorHom a)
        (smallUnstraighteningFunctorHom_projection a) b) ≫
      (smallLeftUnstraighteningFiberIso G b).hom ≫
        (leftUnstraighteningFiberIso G (ULift.up b)).hom =
    (smallLeftUnstraighteningFiberIso F b).hom ≫
      vertexFiberMap (leftUnstraighteningProjection F) (leftUnstraighteningProjection G)
        (unstraighteningFunctorHom a) (unstraighteningFunctorHom_projection a) (ULift.up b) ≫
          (leftUnstraighteningFiberIso G (ULift.up b)).hom := by
    simpa only [← smallUnstraighteningFunctorHom_eq_overMap a, Category.assoc] using! hn
  dsimp only
  rw [hn']
  exact ht

/-- 概要：同じ商上の全空間射を、元の単体圏頂点の実 fiber へ制限する。
方針：元の fiber 包含と同じ全空間射を合成して指定商 fiber へ持ち上げる。
規約：底は元の初頂点写像と q の像に固定する。
使われ方：K-B-S の指定全空間比較の全 fiber 作用。 -/
def weakSpanKanQuotientSimplexFiberMap (c : TransportSimplexCategory B.obj) :=
  vertexFiberLift (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
    ((transportSimplexFirstVertexMap B.obj ≫ q.hom).app (Opposite.op ⦋0⦌) (nerveVertex c))
    (vertexFiberι (smallLeftUnstraighteningProjection (weakSpanKanCoherentDiagram i x))
      (nerveVertex c) ≫ weakSpanKanQuotientSimplexUnstraighteningMap h x)
    (by
      rw [Category.assoc, weakSpanKanQuotientSimplexUnstraighteningMap_projection,
        ← Category.assoc, vertexFiberι_comp]
      simp only [SSet.const_comp])

/-- 概要：同じ実 fiber 射は元の全空間比較の厳密な制限。
方針：指定 fiber への持ち上げの回収式を使う。
規約：元の fiber の全単体を保持する。
使われ方：全族単位の回収を同じ全空間射について述べる。 -/
theorem weakSpanKanQuotientSimplexFiberMap_ι (c : TransportSimplexCategory B.obj) :
    weakSpanKanQuotientSimplexFiberMap h x c ≫
      vertexFiberι (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        ((transportSimplexFirstVertexMap B.obj ≫ q.hom).app
          (Opposite.op ⦋0⦌) (nerveVertex c)) =
    vertexFiberι (smallLeftUnstraighteningProjection (weakSpanKanCoherentDiagram i x))
      (nerveVertex c) ≫ weakSpanKanQuotientSimplexUnstraighteningMap h x :=
  vertexFiberLift_ι _ _ _ _

/-- 概要：商上への同じ実射の全 fiber 作用は、指定降下成分の transport と関手同型。
方針：全空間の pointed 成分の等式を fiber へ制限し、同じ比較射の transport 同型を使う。
規約：単位の供給や元の marked span 全族への降下は主張しない。
使われ方：K-B-S の元の全 fiber 単位と同じ商 fiber の指定比較の照合。 -/
def weakSpanKanQuotientSimplexFiberTransportIso (c : TransportSimplexCategory B.obj) :
    let F := weakSpanKanCoherentDiagram i x
    let Q := weakSpanKanQuotientDiagram h x
    let a := (weakSpanKanQuotientDiagram_simplexIso h x).symm.hom
    let b := nerveVertex c
    let y := (transportSimplexFirstVertexMap B.obj ≫ q.hom).app (Opposite.op ⦋0⦌) b
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (weakSpanKanQuotientSimplexFiberMap h x c) ≫
        (smallLeftUnstraighteningFiberIso Q y).hom ≫
          (leftUnstraighteningFiberIso Q (ULift.up y)).hom)
      ((smallLeftUnstraighteningFiberIso F b).hom ≫
        (leftUnstraighteningFiberIso F (ULift.up b)).hom ≫
          edgeTransport pointedSpaceProjection
            (functorEdgeAt (intervalMappingEdgeOfVertex (smallUnstraighteningHomParameter a))
              (ULift.up b))) := by
  let F := weakSpanKanCoherentDiagram i x
  let Q := weakSpanKanQuotientDiagram h x
  let α := transportSimplexFirstVertexMap B.obj ≫ q.hom
  let G := (SSet.uliftFunctor.{u + 1, u}).map α ≫ Q
  let a := (weakSpanKanQuotientDiagram_simplexIso h x).symm.hom
  let b := nerveVertex c
  let y := α.app (Opposite.op ⦋0⦌) b
  have he : (SSet.uliftFunctor.{u + 1, u}).map
      (weakSpanKanQuotientSimplexFiberMap h x c) ≫
      (smallLeftUnstraighteningFiberIso Q y).hom ≫
        (leftUnstraighteningFiberIso Q (ULift.up y)).hom =
    (SSet.uliftFunctor.{u + 1, u}).map
      (vertexFiberMap (smallLeftUnstraighteningProjection F)
        (smallLeftUnstraighteningProjection G) (smallUnstraighteningFunctorHom a)
        (smallUnstraighteningFunctorHom_projection a) b) ≫
      (smallLeftUnstraighteningFiberIso G b).hom ≫
        (leftUnstraighteningFiberIso G (ULift.up b)).hom := by
    apply vertexFiber_hom_ext pointedSpaceProjection (Q.app (Opposite.op ⦋0⦌) (ULift.up y))
    simp only [Category.assoc]
    erw [leftUnstraighteningFiberIso_hom_ι Q (ULift.up y),
      leftUnstraighteningFiberIso_hom_ι G (ULift.up b)]
    rw [← Category.assoc (smallLeftUnstraighteningFiberIso Q y).hom,
      smallLeftUnstraighteningFiberIso_hom_ι,
      ← Category.assoc (smallLeftUnstraighteningFiberIso G b).hom,
      smallLeftUnstraighteningFiberIso_hom_ι]
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc, ← CategoryTheory.Functor.map_comp_assoc,
      weakSpanKanQuotientSimplexFiberMap_ι, vertexFiberMap_ι,
      CategoryTheory.Functor.map_comp_assoc, CategoryTheory.Functor.map_comp_assoc]
    exact congrArg (fun f => (SSet.uliftFunctor.{u + 1, u}).map
      (vertexFiberι (smallLeftUnstraighteningProjection F) b) ≫ f)
      (weakSpanKanQuotientSimplexUnstraighteningMap_pointed h x)
  dsimp only
  rw [he]
  exact weakSpanKanQuotientSimplexComparisonFiberTransportIso h x c

end SerrePositivity.KST.Fibration
