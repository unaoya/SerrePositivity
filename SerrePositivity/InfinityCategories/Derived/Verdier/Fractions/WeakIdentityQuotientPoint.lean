module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakIdentityKanValue
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.WeakSpanKanQuotientDescent
public import SerrePositivity.KST.Fibration.PointedSpaceHomPoint

/-! # 元の恒等 span から、同じ商上の分数図式の実 unstraightening 点を構成する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の x の商像における図式値は、同じ零単体を添字とする strict Kan 分数値と同型。 -/
def weakIdentityQuotientValueIso : VertexIso
    ((weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
      (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)))
    (spaceInfinityVertex ((weakSpanKanDiagram i x).obj
      (transportSimplexIndex (n := ⦋0⦌) x))) := by
  have he : ULift.up.{u + 1} (q.hom.app (Opposite.op ⦋0⦌) x) =
      ULift.up (q.hom.app (Opposite.op ⦋0⦌)
        ((transportSimplexFirstVertexMap B.obj).app (Opposite.op ⦋0⦌)
          (nerveVertex (transportSimplexIndex (n := ⦋0⦌) x)))) :=
    congrArg ULift.up (congrArg (q.hom.app (Opposite.op ⦋0⦌))
      (transportSimplexFirstVertexMap_zeroIndex x).symm)
  exact eqToIso (congrArg HomotopyCategory.mk
    (congrArg ((weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)) he)) ≪≫
      weakSpanKanQuotientDiagram_initialVertexIso h x (transportSimplexIndex (n := ⦋0⦌) x)

/-- 同じ strict Kan 恒等点を一点空間からの元の射として表す。 -/
def weakIdentityNativePointHom :
    HomotopyCategory.mk pointSpaceVertex ⟶
      HomotopyCategory.mk (spaceInfinityVertex ((weakSpanKanDiagram i x).obj
        (transportSimplexIndex (n := ⦋0⦌) x))) :=
  Truncated.HomotopyCategory.homMk (cosliceFiberVertexToEdge
    ((pointedSpaceFiberVertexEquiv _).symm (weakIdentityKanPoint h x))).toTruncated

/-- 商上の図式値の恒等点を、同じ実制限同型を通した一点空間からの射として保持する。 -/
def weakIdentityQuotientPointHom :
    HomotopyCategory.mk pointSpaceVertex ⟶
      HomotopyCategory.mk ((weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x))) :=
  weakIdentityNativePointHom h x ≫ (weakIdentityQuotientValueIso h x).inv

/-- 元の同じ図式値の比較で正規化すると、指定した元の strict Kan 恒等点の射を回収。 -/
theorem weakIdentityQuotientPointHom_normalized :
    weakIdentityQuotientPointHom h x ≫ (weakIdentityQuotientValueIso h x).hom =
      weakIdentityNativePointHom h x := by
  unfold weakIdentityQuotientPointHom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 同じ一点空間からの射を、元の商上の図式値の実 pointed-space fiber 点にする。 -/
def weakIdentityQuotientPointedFiber :
    (vertexFiber pointedSpaceProjection
      ((weakSpanKanQuotientDiagram h x).app (Opposite.op ⦋0⦌)
        (ULift.up (q.hom.app (Opposite.op ⦋0⦌) x)))) _⦋0⦌ :=
  pointedSpaceFiberPointOfHom (weakIdentityQuotientPointHom h x)

/-- 商上の分数図式の、元の小さい unstraightening の同じ fiber 内の恒等点。 -/
def weakIdentityQuotientFiberPoint :
    (vertexFiber (smallLeftUnstraighteningProjection (weakSpanKanQuotientDiagram h x))
      (q.hom.app (Opposite.op ⦋0⦌) x)) _⦋0⦌ :=
  smallUnstraighteningFiberPoint (weakSpanKanQuotientDiagram h x)
    (q.hom.app (Opposite.op ⦋0⦌) x) (weakIdentityQuotientPointedFiber h x)

/-- 選んだ商上の実点の辺の類は、指定した元の恒等点を同じ値の同型で移した射そのもの。 -/
theorem weakIdentityQuotientPointedFiber_hom :
    Truncated.HomotopyCategory.homMk
      (cosliceFiberVertexToEdge (weakIdentityQuotientPointedFiber h x)).toTruncated =
        weakIdentityQuotientPointHom h x := pointedSpaceFiberPointOfHom_hom _

end SerrePositivity.KST.Fibration
