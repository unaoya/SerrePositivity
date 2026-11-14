module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.ProductSimplexElements
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
概要：元の積単体の次数 Over 表示と第一射影を任意の共通上限宇宙で扱う。
方針：元の全単体・作用素と up・down の往復を同じ max 宇宙で評価する。
規約：元の小さい単体集合と指定次数を保持する。
使われ方：一般モデル圏の実 roof 比較の積単体の次数表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver
open CategoryTheory MonoidalCategory Opposite
open scoped _root_.Simplicial
variable (M : SSet.{u}) (n : AsSmall.{max u w} SimplexCategory)

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
abbrev elements := ULiftHom.{max u w} M.Elementsᵒᵖ
/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
abbrev productElements :=
  ULiftHom.{max u w} (M ⊗ SSet.stdSimplex.obj (ULift.down n)).Elementsᵒᵖ

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
def degree : elements.{u, w} M ⥤ AsSmall.{max u w} SimplexCategory where
  obj s := ⟨(ULiftHom.objDown s).unop.obj.unop⟩
  map f := ⟨(ULift.down f).unop.hom.unop⟩

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
def firstComponent : productElements.{u, w} M n ⥤ elements.{u, w} M where
  obj s := ULiftHom.objUp (op (Functor.elementsMk M
    (ULiftHom.objDown s).unop.obj (ULiftHom.objDown s).unop.val.1))
  map f := ⟨Quiver.Hom.op
    { hom := (ULift.down f).unop.hom
      map_val := congrArg Prod.fst (ULift.down f).unop.map_val }⟩

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
def toCostructured : productElements.{u, w} M n ⥤ CostructuredArrow (degree.{u, w} M) n where
  obj s :=
    { left := (firstComponent.{u, w} M n).obj s
      right := ⟨⟨⟩⟩
      hom := ⟨SSet.stdSimplex.objEquiv (ULiftHom.objDown s).unop.val.2⟩ }
  map f := CostructuredArrow.homMk ((firstComponent.{u, w} M n).map f) (by
    apply ULift.ext
    exact congrArg (fun z => SSet.stdSimplex.objEquiv z.2) (ULift.down f).unop.map_val)

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
def fromCostructured : CostructuredArrow (degree.{u, w} M) n ⥤ productElements.{u, w} M n where
  obj s := ULiftHom.objUp (op (Functor.elementsMk _
    (ULiftHom.objDown s.left).unop.obj
    ((ULiftHom.objDown s.left).unop.val, SSet.stdSimplex.objEquiv.symm (ULift.down s.hom))))
  map f := ⟨Quiver.Hom.op
    { hom := (ULift.down f.left).unop.hom
      map_val := by
        apply Prod.ext
        · exact (ULift.down f.left).unop.map_val
        · apply SSet.stdSimplex.objEquiv.injective
          exact congrArg ULift.down (CostructuredArrow.w f) }⟩

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
def equivalence : productElements.{u, w} M n ≌ CostructuredArrow (degree.{u, w} M) n where
  functor := toCostructured.{u, w} M n
  inverse := fromCostructured.{u, w} M n
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
lemma toCostructured_inverse : toCostructured.{u, w} M n ⋙ fromCostructured.{u, w} M n = 𝟭 _ := rfl
/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
lemma fromCostructured_inverse : fromCostructured.{u, w} M n ⋙ toCostructured.{u, w} M n =
  𝟭 _ := rfl
/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
lemma toCostructured_projection : toCostructured.{u, w} M n ⋙
    CostructuredArrow.proj (degree.{u, w} M) n = firstComponent.{u, w} M n := rfl

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
def over : productElements.{u, w} M n ⥤ Over n where
  obj s :=
    { left := (degree.{u, w} M).obj ((firstComponent.{u, w} M n).obj s)
      right := ⟨⟨⟩⟩
      hom := ⟨SSet.stdSimplex.objEquiv (ULiftHom.objDown s).unop.val.2⟩ }
  map f := Over.homMk ((degree.{u, w} M).map ((firstComponent.{u, w} M n).map f)) (by
    apply ULift.ext
    exact congrArg (fun z => SSet.stdSimplex.objEquiv z.2) (ULift.down f).unop.map_val)

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
lemma over_projection : over.{u, w} M n ⋙ Over.forget n = firstComponent.{u, w} M n ⋙
  degree.{u, w} M := rfl

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
lemma over_arrow (s : productElements.{u, w} M n) :
    ULift.down ((over.{u, w} M n).obj s).hom =
      SSet.stdSimplex.objEquiv (ULiftHom.objDown s).unop.val.2 := rfl

/-- 概要：同じ積単体の全要素と次数表示を任意上限の宇宙で回収する。
方針：元の各成分と up・down の全作用素の往復を評価する。
規約：同じ元の単体。使われ方：実 roof の同じ次数比較への接続。 -/
def nerveIso : nerve (productElements.{u, w} M n) ≅
  nerve (CostructuredArrow (degree.{u, w} M) n) where
  hom := { app _ := ↾fun σ => σ ⋙ toCostructured.{u, w} M n
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun σ => σ ⋙ fromCostructured.{u, w} M n
           naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexUniverseOver
