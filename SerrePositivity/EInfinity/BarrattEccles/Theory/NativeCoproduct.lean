module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CoproductNativeUniversal
public import SerrePositivity.InfinityCategories.HomotopyLimits.BinaryDiscreteShape
public import SerrePositivity.InfinityCategories.Core.ReindexSliceUnder

/-!
# 指定余積関手の native な余極限錐

概要：HA 3.2.4.7 の二項余積を、界面の指定二点図式上で供給する。
方針：二点の離散 nerve の同型で余錐を引き戻し、頂点を正規化する。
規約：既存の coprodWith の値と同じ cofibrant な代表の余積を使う。
使われ方：EInfinityTheory の coprodWith_cocone の実例。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open scoped Simplicial

/-- 同じ宇宙の ULift を、元の単体集合と厳密に比較する。 -/
def binaryShapeSelfLiftIso (K : SSet.{u + 1}) :
    K ≅ SSet.uliftFunctor.{u + 1, u + 1}.obj K :=
  NatIso.ofComponents (fun _ => Equiv.toIso Equiv.ulift.symm) (by intros; rfl)

/-- 第一頂点を true、第二頂点を false とする、同じ二点の形状同型。 -/
def cAlgBinaryShapeIso : (Δ[0] : SSet.{u + 1}) ⨿ Δ[0] ≅
    SSet.uliftFunctor.{u + 1, u + 1}.obj (nerve (Discrete (ULift.{u + 1} Bool))) :=
  coprod.braiding _ _ ≪≫ binaryDiscreteNerveIso ≪≫ binaryShapeSelfLiftIso _

/-- 形状同型の第一制限は、第一の指定頂点。 -/
lemma cAlgBinaryShapeIso_left : coprod.inl ≫ cAlgBinaryShapeIso.{u}.hom =
    SSet.const (ULift.up (nerveVertex (Discrete.mk (ULift.up true)))) := by
  simp only [cAlgBinaryShapeIso, Iso.trans_hom, coprod.braiding_hom,
    binaryDiscreteNerveIso, coproductToBinaryDiscrete, coprod.inl_desc_assoc, coprod.inr_desc_assoc]
  ext n s
  rfl

/-- 形状同型の第二制限は、第二の指定頂点。 -/
lemma cAlgBinaryShapeIso_right : coprod.inr ≫ cAlgBinaryShapeIso.{u}.hom =
    SSet.const (ULift.up (nerveVertex (Discrete.mk (ULift.up false)))) := by
  simp only [cAlgBinaryShapeIso, Iso.trans_hom, coprod.braiding_hom,
    binaryDiscreteNerveIso, coproductToBinaryDiscrete, coprod.inl_desc_assoc, coprod.inr_desc_assoc]
  ext n s
  rfl

variable (A : Type u) [CommRing A] (X Y : CAlgSimplicialCategory A)

/-- 二点の離散図式を、界面の元の二点図式へ同定する。 -/
lemma cAlgBinaryShape_diagram :
    cAlgBinaryShapeIso.hom ≫ strictCoherentDiagram (cAlgBinaryDiagram A X Y) =
      binaryPointDiagram (cAlgVertexEquiv A X) (cAlgVertexEquiv A Y) := by
  apply coprod.hom_ext
  · rw [← Category.assoc, cAlgBinaryShapeIso_left, binaryPointDiagram, coprod.inl_desc]
    apply SSet.yonedaEquiv.injective
    exact strictCoherentDiagram_vertex (cAlgBinaryDiagram A X Y) ⟨⟨true⟩⟩
  · rw [← Category.assoc, cAlgBinaryShapeIso_right, binaryPointDiagram, coprod.inr_desc]
    apply SSet.yonedaEquiv.injective
    exact strictCoherentDiagram_vertex (cAlgBinaryDiagram A X Y) ⟨⟨false⟩⟩

/-- 同じ代表の余積を頂点とする、指定二点図式上の余極限錐。 -/
def cAlgNativeCoprodCocone :
    JoinCocone (binaryPointDiagram (cAlgVertexEquiv A X) (cAlgVertexEquiv A Y)) :=
  coherentCoconeOfDiagramEq (cAlgBinaryShape_diagram A X Y)
    ((strictNativeCocone (cAlgBinaryCocone A X Y)).reindexIso cAlgBinaryShapeIso)

/-- 再添字した頂点も、元の余積関手の指定した値。 -/
lemma cAlgNativeCoprodCocone_vertex : (cAlgNativeCoprodCocone A X Y).vertex =
    atVertex (barrattEcclesCoprodWith A (cAlgVertexEquiv A Y)) (cAlgVertexEquiv A X) := by
  rw [cAlgNativeCoprodCocone, coherentCoconeOfDiagramEq_vertex]
  change (strictNativeCocone (cAlgBinaryCocone A X Y)).vertex = _
  rw [strictNativeCocone_vertex]
  change cAlgVertexEquiv A
    (show CAlgSimplicialCategory A from (cofibrantAlgebraDKCoprodWith A Y).obj X) = _
  simpa [barrattEcclesCoprodWith] using (cAlgCoprodWithModel_vertex A Y X).symm

/-- 再添字は余極限性を保つ。 -/
lemma cAlgNativeCoprodCocone_isColimit : IsColimitCone (cAlgNativeCoprodCocone A X Y) := by
  apply (coherentCoconeOfDiagramEq_isColimit_iff (cAlgBinaryShape_diagram A X Y) _).mp
  exact (isColimitCone_iff_reindexIso _ _).mp (cAlgBinaryCocone_isColimit A X Y)

/-- HA 3.2.4.7 の二項余積錐。EInfinityTheory の指定した欄を供給する。 -/
def barrattEcclesCoprodWith_cocone (x y : (CAlg_R A) _⦋0⦌) :
    { c : JoinCocone (binaryPointDiagram x y) //
      c.vertex = atVertex (barrattEcclesCoprodWith A y) x ∧ IsColimitCone c } := by
  let X := (cAlgVertexEquiv A).symm x
  let Y := (cAlgVertexEquiv A).symm y
  have h : binaryPointDiagram (cAlgVertexEquiv A X) (cAlgVertexEquiv A Y) =
      binaryPointDiagram x y := by simp [X, Y]
  refine ⟨coherentCoconeOfDiagramEq h (cAlgNativeCoprodCocone A X Y), ?_, ?_⟩
  · rw [coherentCoconeOfDiagramEq_vertex, cAlgNativeCoprodCocone_vertex]
    simp [X, Y]
  · exact (coherentCoconeOfDiagramEq_isColimit_iff h _).mp
      (cAlgNativeCoprodCocone_isColimit A X Y)

end SerrePositivity.EInfinity.BarrattEccles
