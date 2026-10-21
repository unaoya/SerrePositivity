module

public import SerrePositivity.EInfinity.FrameHom.FrameArrowCategory
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ResolutionHom
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-!
# 元の frame Hom の全単体と固定終域の矢の照合

概要：元の反対要素圏を同じ frame の costructured arrow 圏と同値にする。
方針：元の単体・元の単体作用素をそのまま矢・可換三角形へ送る。
規約：固定終域と元の右脚を保持し、全矢の comma 圏への包含も厳密に供給する。
使われ方：既存 sourceFrameHom 比較の全体への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory Opposite SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C) (Y : C)

def elementsToCostructured : (((cosimplicialHom A).obj Y).Elements)ᵒᵖ ⥤
    CostructuredArrow A Y where
  obj s := CostructuredArrow.mk s.unop.val
  map f := CostructuredArrow.homMk f.unop.hom.unop f.unop.map_val

def costructuredToElements : CostructuredArrow A Y ⥤
    (((cosimplicialHom A).obj Y).Elements)ᵒᵖ where
  obj s := op (Functor.elementsMk _ (op s.left) s.hom)
  map f := Quiver.Hom.op { hom := f.left.op, map_val := by exact CostructuredArrow.w f }

def elementsCostructuredEquivalence : (((cosimplicialHom A).obj Y).Elements)ᵒᵖ ≌
    CostructuredArrow A Y where
  functor := elementsToCostructured A Y
  inverse := costructuredToElements A Y
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  counitIso := NatIso.ofComponents (fun _ => CostructuredArrow.isoMk (Iso.refl _))

def fixedTargetInclusion : CostructuredArrow A Y ⥤ Total A where
  obj s := ⟨s.left, Y, s.hom⟩
  map f := { left := f.left, right := 𝟙 Y, w := by simp }

lemma fixedTargetInclusion_degree : fixedTargetInclusion A Y ⋙ degree A =
    CostructuredArrow.proj A Y := rfl
lemma fixedTargetInclusion_target : fixedTargetInclusion A Y ⋙ target A =
    (Functor.const (CostructuredArrow A Y)).obj Y := rfl

def elementsTotal : (((cosimplicialHom A).obj Y).Elements)ᵒᵖ ⥤ Total A :=
  elementsToCostructured A Y ⋙ fixedTargetInclusion A Y

lemma elementsTotal_degree : elementsTotal A Y ⋙ degree A =
    (Functor.Elements.π ((cosimplicialHom A).obj Y)).leftOp := rfl
lemma elementsTotal_target : elementsTotal A Y ⋙ target A =
    (Functor.const (((cosimplicialHom A).obj Y).Elements)ᵒᵖ).obj Y := rfl
lemma elementsTotal_rightLeg (s : (((cosimplicialHom A).obj Y).Elements)ᵒᵖ) :
    (rightLeg A).app ((elementsTotal A Y).obj s) = s.unop.val := rfl

end SerrePositivity.EInfinity.FrameHom.FrameArrows
