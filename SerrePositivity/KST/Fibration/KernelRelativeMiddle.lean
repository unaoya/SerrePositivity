module
public import SerrePositivity.KST.Fibration.WeakCofiberVertices

/-! # 両端が核に入る相対 cofiber 図式の中間評価

商での実 cofiber 列の二対象の消滅から、中間対象も核に入ることを導く。
中間評価を核に値を持つ完全関手に制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 両端が商で零になる元の cofiber 四角形の中間頂点も商で零である。 -/
lemma kernelRelativeCofiber_middle_mem {B C : StableCategory.{u}} (q : ExactMap B C)
    (w : (cofiberDiagrams B.obj) _⦋0⦌)
    (hw : (relativeCofiberPredicate (kernelClosedPredicate q)
      (kernelClosedPredicate q)).predicate w) :
    (kernelClosedPredicate q).predicate
      ((cofiberStableMiddle (sInputModel B)).val.app (Opposite.op ⦋0⦌) w) := by
  let t := (vertexCofiberSquare w).toZeroTriangle
  have h₀ : IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) (squareVertex t.square 0 0)) :=
    (congrArg (fun x => IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) x))
      (cofiberVertex_corner B w
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0))).mp hw.1
  have h₂ : IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) (squareVertex t.square 1 1)) :=
    (congrArg (fun x => IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) x))
      (cofiberVertex_corner B w
        (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1))).mp hw.2
  have hm := ZeroTriangle.zero_middle_of_zero_source_cofiber
    (t.map q.hom (IsExactFunctor.preservesZero (F := q.hom)))
    (IsExactFunctor.preservesCofiber (F := q.hom) t (vertexCofiberSquare w).isPushout) h₀ h₂
  exact (congrArg (fun x => IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) x))
    (cofiberVertex_corner B w
      (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0))).mpr hm

/-- E(ker q,B,ker q) の元の中間評価を核部分圏へ制限する。 -/
def kernelRelativeMiddleMap {B C : StableCategory.{u}} (q : ExactMap B C) :
    relativeCofiberDiagrams (kernelClosedPredicate q) (kernelClosedPredicate q) ⟶
      closedSubcategory (kernelClosedPredicate q) :=
  fullSubcomplexLift (kernelClosedPredicate q).predicate
    ((relativeCofiberInclusion (kernelClosedPredicate q) (kernelClosedPredicate q)).val ≫
      (cofiberStableMiddle (sInputModel B)).val)
    (fun w => kernelRelativeCofiber_middle_mem q w.val (fullSubcomplexOnVertices_vertex w))

/-- 核への制限を含めると元の中間評価を厳密に回収する。 -/
lemma kernelRelativeMiddleMap_ι {B C : StableCategory.{u}} (q : ExactMap B C) :
    kernelRelativeMiddleMap q ≫ (closedStableInclusion (kernelClosedPredicate q)).val =
      (relativeCofiberInclusion (kernelClosedPredicate q) (kernelClosedPredicate q)).val ≫
        (cofiberStableMiddle (sInputModel B)).val := rfl

/-- 同じ中間評価は核に値を持つ完全関手である。 -/
def kernelRelativeMiddle {B C : StableCategory.{u}} (q : ExactMap B C) :
    relativeCofiberStableModel (kernelClosedPredicate q) (kernelClosedPredicate q) ⟶
      closedStableModel (kernelClosedPredicate q) :=
  ⟨kernelRelativeMiddleMap q, by
    apply preservesCofiberData_fullSubcomplex_of_comp (kernelClosedPredicate q).predicate
    change PreservesCofiberData
      (kernelRelativeMiddleMap q ≫ (closedStableInclusion (kernelClosedPredicate q)).val)
    rw [kernelRelativeMiddleMap_ι]
    exact PreservesCofiberData.comp
      (relativeCofiberInclusion (kernelClosedPredicate q) (kernelClosedPredicate q)).property
      (cofiberStableMiddle (sInputModel B)).property⟩

end SerrePositivity.KST.Fibration
