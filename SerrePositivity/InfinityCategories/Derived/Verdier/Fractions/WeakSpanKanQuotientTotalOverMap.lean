module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanQuotientTotalResolution
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningRepresentation
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorUnitHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.EdgeTransportPointLift

/-!
概要：供給された単体圏単位から降下した元の marked span 全族の比較を、底 q 上で厳密化する。
方針：既存の初頂点局所化の充満忠実性で底比較を戻し、関手空間の left fibration で輸送する。
規約：Ind-S (5) の単位と厳密な底条件に条件付き。新しい局所化・商・分類 API は追加しない。
使われ方：K-B-S の元の全族から同じ商図式への実写像。全 fiber 単位・指定恒等点の回収は別工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)
  (f : CategoryTheory.Limits.pullback (markedSpanFamilyProjection B.obj (weakEquivalences i) x)
    (transportSimplexFirstVertexMap B.obj) ⟶
      smallLeftUnstraightening (weakSpanKanCoherentDiagram i x))
  (hf : f ≫ smallLeftUnstraighteningProjection (weakSpanKanCoherentDiagram i x) =
    weakSpanSimplexProjection i x)

/-- 概要：元の降下比較の底は、元の全族射影と q に全入力で自然同型。
方針：同じ指定降下同型を射影し、初頂点局所化の充満忠実性で戻す。
規約：単位と厳密な底条件に条件付き。
使われ方：底 q を厳密に保存する全族射への輸送。 -/
def weakSpanKanQuotientTotalDescendBaseIso :
    FunctorIso
      (weakSpanKanQuotientTotalDescend h x f hf ≫
        smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
      (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom) := by
  have e := (weakSpanKanQuotientTotalDescendIso h x f hf).postcomp
    (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
  rw [Category.assoc, weakSpanKanQuotientTotalSimplexMap_projection h x f hf] at e
  exact (localization_pre_isFullyFaithful
    (transportSimplexFirstVertexMap_isLocalization
      (markedSpanFamily B.obj (weakEquivalences i) x)) C.obj).preimageVertexIso e

/-- 概要：同じ降下比較を底 q へ輸送した、相対関手空間の実頂点。
方針：後合成の left fibration で指定底比較の同じ代表辺に沿って輸送する。
規約：単位の存在は主張せず、元の降下比較を始点として保持する。
使われ方：同じ全族からの厳密な底上の実射を回収する。 -/
def weakSpanKanQuotientTotalOverVertex :
    (relativeFunctorSpace
      (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
      (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)) _⦋0⦌ :=
  (edgeTransport ((ihom (markedSpanFamily B.obj (weakEquivalences i) x)).map
      (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)))
    (FunctorIso.edge (weakSpanKanQuotientTotalDescendBaseIso h x f hf))).app
      (Opposite.op ⦋0⦌)
      (relativeFunctorVertex
        (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (weakSpanKanQuotientTotalDescend h x f hf ≫
          smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
        (weakSpanKanQuotientTotalDescend h x f hf) rfl)

/-- 概要：元の全族から同じ商図式への、底 q を厳密に保つ実射とその証拠。
方針：同じ相対関手空間の頂点を元の射へ戻す。
規約：単体圏単位と底条件に条件付き。全 fiber 単位の回収はまだ含めない。
使われ方：K-B-S の指定底を持つ全族射の利用側。 -/
def weakSpanKanQuotientTotalOverMap :
    {g : markedSpanFamily B.obj (weakEquivalences i) x ⟶
        smallLeftUnstraightening (weakSpanKanQuotientDiagram h x) //
      g ≫ smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x) =
        markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom} :=
  (relativeFunctorVertexEquiv
    (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
    (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)).symm
      (weakSpanKanQuotientTotalOverVertex h x f hf)

/-- 概要：供給単位から構成する、元の marked span 全族の同じ実商比較射。
方針：底 q への輸送で得た同じ射を使う。
規約：単位の供給に条件付き。元の Kan 単位・指定恒等点の回収はまだ主張しない。
使われ方：K-B-S の全族写像の候補。 -/
def weakSpanKanQuotientTotalMap := (weakSpanKanQuotientTotalOverMap h x f hf).val

/-- 概要：同じ元の全族写像は底 q を厳密に保存する。
方針：同じ相対関手空間の頂点の固定条件を回収する。
規約：単位と底条件に条件付き。別の全族射を選び直さない。
使われ方：Sp 向けの全族写像の厳密な底条件。 -/
theorem weakSpanKanQuotientTotalMap_projection :
    weakSpanKanQuotientTotalMap h x f hf ≫
        smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x) =
      markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom :=
  (weakSpanKanQuotientTotalOverMap h x f hf).property

/-- 概要：同じ全族写像を相対頂点へ戻すと、指定底比較で輸送した元の頂点を回収する。
方針：相対頂点と底上の射の全単射の往復を使う。
規約：指定された輸送を変更しない。
使われ方：元の降下比較と同じ全族射の自然同型を構成する。 -/
theorem weakSpanKanQuotientTotalMap_vertex :
    relativeFunctorVertex
      (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
      (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)
      (weakSpanKanQuotientTotalMap h x f hf) (weakSpanKanQuotientTotalMap_projection h x f hf) =
    weakSpanKanQuotientTotalOverVertex h x f hf :=
  (relativeFunctorVertexEquiv
    (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
    (markedSpanFamilyProjection B.obj (weakEquivalences i) x ≫ q.hom)).apply_symm_apply _

/-- 概要：底 q を厳密に保つ同じ全族射は、元の降下比較と全関手空間で自然同型。
方針：底比較の代表辺の輸送を元の相対頂点で評価し、可逆性を left fibration で反映する。
規約：供給単位に条件付き。fiber 内比較の全整合性はまだ主張しない。
使われ方：元の単体圏上の指定比較を同じ全族射へ追跡する。 -/
def weakSpanKanQuotientTotalMapDescendIso :
    FunctorIso (weakSpanKanQuotientTotalDescend h x f hf)
      (weakSpanKanQuotientTotalMap h x f hf) := by
  let E := markedSpanFamily B.obj (weakEquivalences i) x
  let U := smallLeftUnstraightening (weakSpanKanQuotientDiagram h x)
  let p := smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x)
  let P := (ihom E).map p
  let g := weakSpanKanQuotientTotalDescend h x f hf
  let e := SSet.Edge.ofTruncated
    (FunctorIso.edge (weakSpanKanQuotientTotalDescendBaseIso h x f hf))
  let v := relativeFunctorVertex p (g ≫ p) g rfl
  let H := HomotopyLimits.exists_edge_of_transport_point P e
    (edgeTransport P e) (edgeTransport_isTransport P e) v
  let k := Classical.choose H
  have hk := Classical.choose_spec H
  have hi : IsInvertibleEdge k := leftFibration_reflects_invertibleEdge P k
    ((isInvertibleEdge_congr hk).mpr
      (FunctorIso.edge_isInvertible (weakSpanKanQuotientTotalDescendBaseIso h x f hf)))
  have hw : functorVertex (weakSpanKanQuotientTotalMap h x f hf) =
      (weakSpanKanQuotientTotalOverVertex h x f hf).val :=
    congrArg Subtype.val (weakSpanKanQuotientTotalMap_vertex h x f hf)
  let k' := k.ofEq rfl hw.symm
  have hk' : IsInvertibleEdge k' :=
    (isInvertibleEdge_congr (show k'.edge = k.edge from rfl)).mpr hi
  letI : IsIso (Truncated.HomotopyCategory.homMk k'.toTruncated) := hk'
  exact asIso (Truncated.HomotopyCategory.homMk k'.toTruncated)

/-- 概要：厳密な底上の同じ全族射は元の単体圏の指定実比較を自然同型で回収する。
方針：同じ底輸送の自然同型を初頂点で制限し、元の局所化因子化同型に合成する。
規約：単位に条件付き。全 fiber 単位の回収とは別の比較。
使われ方：K-B-S の元の全族写像と供給単位との同じ制限の追跡。 -/
def weakSpanKanQuotientTotalMapRestrictionIso :
    FunctorIso
      (transportSimplexFirstVertexMap (markedSpanFamily B.obj (weakEquivalences i) x) ≫
        weakSpanKanQuotientTotalMap h x f hf)
      (weakSpanKanQuotientTotalSimplexMap h x f) :=
  ((weakSpanKanQuotientTotalMapDescendIso h x f hf).precomp
    (transportSimplexFirstVertexMap (markedSpanFamily B.obj (weakEquivalences i) x))).symm ≪≫
      weakSpanKanQuotientTotalDescendIso h x f hf

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalDescendBaseIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalDescendBaseIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalDescendBaseIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMap := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMap

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMapDescendIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMapDescendIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMapDescendIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMapRestrictionIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMapRestrictionIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMapRestrictionIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMap_projection := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMap_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMap_vertex := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMap_vertex

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalOverMap (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalOverMap := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalOverMap

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalOverVertex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalOverVertex := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalOverVertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalDescendBaseIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalDescendBaseIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalDescendBaseIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalDescendBaseIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalDescendBaseIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalDescendBaseIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalDescendBaseIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalDescendBaseIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalDescendBaseIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalDescendBaseIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalDescendBaseIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalDescendBaseIso._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMapDescendIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMapDescendIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMapDescendIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMapDescendIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMapDescendIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMapDescendIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMapDescendIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMapDescendIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMapDescendIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMapDescendIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMapDescendIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMapDescendIso._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMapDescendIso._proof_7 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMapDescendIso._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalMapDescendIso._proof_8 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalMapDescendIso._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalOverVertex._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalOverVertex._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanKanQuotientTotalOverVertex._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanKanQuotientTotalOverVertex._proof_2
