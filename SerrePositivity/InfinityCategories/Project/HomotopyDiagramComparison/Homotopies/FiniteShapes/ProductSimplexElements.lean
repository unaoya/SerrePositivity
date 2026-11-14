module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# 元の M×Δ[n] の全単体と次数へ向かう矢の圏

概要：積の全単体・全作用素を、元の M の単体から n へ向かう次数射と同定する。
方針：標準単体の全単射で第二成分を同じ順序写像へ戻す。
規約：元の M・指定 n・第一成分・元の作用素を保持する。
使われ方：実屋根の Quillen A slice の元の有限次数モデル。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexElements
open CategoryTheory MonoidalCategory Opposite
open scoped _root_.Simplicial
variable (M : SSet.{u}) (n : SimplexCategory)

abbrev degree := (Functor.Elements.π M).leftOp

def toCostructured : (M ⊗ SSet.stdSimplex.obj n).Elementsᵒᵖ ⥤
    CostructuredArrow (degree M) n where
  obj s := CostructuredArrow.mk (Y := op (Functor.elementsMk M s.unop.obj s.unop.val.1))
    (SSet.stdSimplex.objEquiv s.unop.val.2)
  map f := CostructuredArrow.homMk
    (Quiver.Hom.op { hom := f.unop.hom, map_val := congrArg Prod.fst f.unop.map_val }) (by
      exact congrArg (fun z => SSet.stdSimplex.objEquiv z.2) f.unop.map_val)

def fromCostructured : CostructuredArrow (degree M) n ⥤
    (M ⊗ SSet.stdSimplex.obj n).Elementsᵒᵖ where
  obj s := op (Functor.elementsMk _ s.left.unop.obj
    (s.left.unop.val, SSet.stdSimplex.objEquiv.symm s.hom))
  map f := Quiver.Hom.op
    { hom := f.left.unop.hom
      map_val := by
        apply Prod.ext
        · exact f.left.unop.map_val
        · apply SSet.stdSimplex.objEquiv.injective
          exact CostructuredArrow.w f }

def equivalence : (M ⊗ SSet.stdSimplex.obj n).Elementsᵒᵖ ≌
    CostructuredArrow (degree M) n where
  functor := toCostructured M n
  inverse := fromCostructured M n
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))

lemma toCostructured_arrow (s : (M ⊗ SSet.stdSimplex.obj n).Elementsᵒᵖ) :
    ((toCostructured M n).obj s).hom = SSet.stdSimplex.objEquiv s.unop.val.2 := rfl

lemma toCostructured_first (s : (M ⊗ SSet.stdSimplex.obj n).Elementsᵒᵖ) :
    ((toCostructured M n).obj s).left.unop.val = s.unop.val.1 := rfl

def firstComponent : (M ⊗ SSet.stdSimplex.obj n).Elementsᵒᵖ ⥤ M.Elementsᵒᵖ where
  obj s := op (Functor.elementsMk M s.unop.obj s.unop.val.1)
  map f := Quiver.Hom.op { hom := f.unop.hom, map_val := congrArg Prod.fst f.unop.map_val }

lemma toCostructured_projection : toCostructured M n ⋙
    CostructuredArrow.proj (degree M) n = firstComponent M n := rfl

lemma toCostructured_fromCostructured : toCostructured M n ⋙ fromCostructured M n = 𝟭 _ := rfl
lemma fromCostructured_toCostructured : fromCostructured M n ⋙ toCostructured M n = 𝟭 _ := rfl

def nerveIso : nerve ((M ⊗ SSet.stdSimplex.obj n).Elementsᵒᵖ) ≅
    nerve (CostructuredArrow (degree M) n) where
  hom := nerveMap (toCostructured M n)
  inv := nerveMap (fromCostructured M n)
  hom_inv_id := rfl
  inv_hom_id := rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexElements
