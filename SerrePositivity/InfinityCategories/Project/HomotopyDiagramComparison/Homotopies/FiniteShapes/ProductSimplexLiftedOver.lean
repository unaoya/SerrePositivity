module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.ProductSimplexElements
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.EssentiallySmall

/-!
# 元の積単体の Hom を上げた次数 Over モデル

概要：元の M×Δ[n] の反対要素圏を、同じ AsSmall Δ の次数射の圏へ移す。
方針：単体・作用素を変更せず、Hom の ULift と標準単体の表示だけを往復する。
規約：元の M、指定 n、第一成分と次数の矢を保持する。
使われ方：実屋根 slice の次数モデルへの全単体の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexLiftedOver
open CategoryTheory MonoidalCategory Opposite
open scoped _root_.Simplicial
variable (M : SSet.{u}) (n : AsSmall.{u + 1} SimplexCategory)

abbrev elements := ULiftHom.{u + 1} M.Elementsᵒᵖ
abbrev productElements :=
  ULiftHom.{u + 1} (M ⊗ SSet.stdSimplex.obj (ULift.down n)).Elementsᵒᵖ

def degree : elements M ⥤ AsSmall.{u + 1} SimplexCategory where
  obj s := ⟨(ULiftHom.objDown s).unop.obj.unop⟩
  map f := ⟨(ULift.down f).unop.hom.unop⟩

def firstComponent : productElements M n ⥤ elements M where
  obj s := ULiftHom.objUp (op (Functor.elementsMk M
    (ULiftHom.objDown s).unop.obj (ULiftHom.objDown s).unop.val.1))
  map f := ⟨Quiver.Hom.op
    { hom := (ULift.down f).unop.hom
      map_val := congrArg Prod.fst (ULift.down f).unop.map_val }⟩

def toCostructured : productElements M n ⥤ CostructuredArrow (degree M) n where
  obj s :=
    { left := (firstComponent M n).obj s
      right := ⟨⟨⟩⟩
      hom := ⟨SSet.stdSimplex.objEquiv (ULiftHom.objDown s).unop.val.2⟩ }
  map f := CostructuredArrow.homMk ((firstComponent M n).map f) (by
    apply ULift.ext
    exact congrArg (fun z => SSet.stdSimplex.objEquiv z.2) (ULift.down f).unop.map_val)

def fromCostructured : CostructuredArrow (degree M) n ⥤ productElements M n where
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

def equivalence : productElements M n ≌ CostructuredArrow (degree M) n where
  functor := toCostructured M n
  inverse := fromCostructured M n
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))

lemma toCostructured_inverse : toCostructured M n ⋙ fromCostructured M n = 𝟭 _ := rfl
lemma fromCostructured_inverse : fromCostructured M n ⋙ toCostructured M n = 𝟭 _ := rfl
lemma toCostructured_projection : toCostructured M n ⋙
    CostructuredArrow.proj (degree M) n = firstComponent M n := rfl

def over : productElements M n ⥤ Over n where
  obj s :=
    { left := (degree M).obj ((firstComponent M n).obj s)
      right := ⟨⟨⟩⟩
      hom := ⟨SSet.stdSimplex.objEquiv (ULiftHom.objDown s).unop.val.2⟩ }
  map f := Over.homMk ((degree M).map ((firstComponent M n).map f)) (by
    apply ULift.ext
    exact congrArg (fun z => SSet.stdSimplex.objEquiv z.2) (ULift.down f).unop.map_val)

lemma over_projection : over M n ⋙ Over.forget n = firstComponent M n ⋙ degree M := rfl

lemma over_arrow (s : productElements M n) :
    ULift.down ((over M n).obj s).hom =
      SSet.stdSimplex.objEquiv (ULiftHom.objDown s).unop.val.2 := rfl

def nerveIso : nerve (productElements M n) ≅ nerve (CostructuredArrow (degree M) n) where
  hom := { app _ := ↾fun σ => σ ⋙ toCostructured M n
           naturality _ _ _ := rfl }
  inv := { app _ := ↾fun σ => σ ⋙ fromCostructured M n
           naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ProductSimplexLiftedOver
