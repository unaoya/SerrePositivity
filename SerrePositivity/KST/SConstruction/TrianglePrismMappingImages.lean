module
public import SerrePositivity.KST.SConstruction.TrianglePrismStaircase
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.MapSmallness
public import SerrePositivity.KST.Spectra.CoherentSimplexCompositionFaces

/-! # 同じ合成 prism の三つの coherent 三単体
概要：元の二単体 prism の三単体像と共有面を、その両端の同じ対象へ照合する。
方針：元の写像の単体自然性と零頂点での対象評価を使う。
規約：像の元の辺・面を保持し、終点の対象を選び直さない。
使われ方：同じ Hom 内の三つの実正方形を作る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
  (Q : (Δ[2] : SSet.{max u v}) ⊗ Δ[1] ⟶ SimplicialNerve C)

/-- 元の合成 prism の三つの coherent 三単体の実像。 -/
def trianglePrismImage (q : Fin 3) : (SimplicialNerve C) _⦋3⦌ :=
  Q.app (Opposite.op ⦋3⦌) (trianglePrismTetrahedron q)

/-- 三つの三単体の共通始点は、元の prism の左下頂点の同じ対象。 -/
def trianglePrismSource : C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (Q.app (Opposite.op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 3), SSet.stdSimplex.obj₀Equiv.symm (0 : Fin 2)))

/-- 三つの三単体の共通終点は、元の prism の右上頂点の同じ対象。 -/
def trianglePrismTarget : C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (Q.app (Opposite.op ⦋0⦌)
    (SSet.stdSimplex.obj₀Equiv.symm (2 : Fin 3), SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)))

/-- 三単体の始点は、共有する元の左下対象を厳密に回収する。 -/
lemma trianglePrismImage_source (q : Fin 3) :
    (trianglePrismImage Q q).obj (.mk (ULift.up 0)) = trianglePrismSource Q := by
  rw [trianglePrismImage, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMap_simplex_obj]
  fin_cases q <;> rfl

/-- 三単体の終点は、共有する元の右上対象を厳密に回収する。 -/
lemma trianglePrismImage_target (q : Fin 3) :
    (trianglePrismImage Q q).obj (.mk (ULift.up 3)) = trianglePrismTarget Q := by
  rw [trianglePrismImage, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMap_simplex_obj]
  fin_cases q <;> rfl

/-- 元の三つの Hom は、元の共通両端の同じ Hom である。 -/
lemma trianglePrismImage_hom (q : Fin 3) :
    SimplicialCategory.sHom ((trianglePrismImage Q q).obj (.mk (ULift.up 0)))
      ((trianglePrismImage Q q).obj (.mk (ULift.up 3))) =
      SimplicialCategory.sHom (trianglePrismSource Q) (trianglePrismTarget Q) :=
  congrArg₂ SimplicialCategory.sHom (trianglePrismImage_source Q q) (trianglePrismImage_target Q q)

/-- 元の prism の指定面は、同じ coherent 三単体の指定面を厳密に回収する。 -/
lemma trianglePrismImage_face {q : Fin 3} {i : Fin 4}
    {p : ((Δ[2] : SSet.{max u v}) ⊗ Δ[1]) _⦋2⦌}
    (h : ((Δ[2] : SSet.{max u v}) ⊗ Δ[1]).δ i (trianglePrismTetrahedron q) = p) :
    (SimplicialNerve C).δ i (trianglePrismImage Q q) = Q.app (Opposite.op ⦋2⦌) p := by
  exact (NatTrans.naturality_apply Q (SimplexCategory.δ i).op
    (trianglePrismTetrahedron q)).symm.trans (congrArg (Q.app (Opposite.op ⦋2⦌)) h)

/-- 最初と中央の三単体像は、同じ元の内側三角形を共有する。 -/
lemma trianglePrismImage_shared_first :
    (SimplicialNerve C).δ 1 (trianglePrismImage Q 0) =
      (SimplicialNerve C).δ 1 (trianglePrismImage Q 1) := by
  exact (trianglePrismImage_face Q trianglePrismTetrahedron_shared_first).trans
    (trianglePrismImage_face Q rfl).symm

/-- 中央と最後の三単体像も、同じ元の内側三角形を共有する。 -/
lemma trianglePrismImage_shared_second :
    (SimplicialNerve C).δ 2 (trianglePrismImage Q 1) =
      (SimplicialNerve C).δ 2 (trianglePrismImage Q 2) := by
  exact (trianglePrismImage_face Q trianglePrismTetrahedron_shared_second).trans
    (trianglePrismImage_face Q rfl).symm

end SerrePositivity.KST.SConstruction
