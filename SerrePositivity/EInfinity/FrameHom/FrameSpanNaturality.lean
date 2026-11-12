module

public import SerrePositivity.EInfinity.FrameHom.FrameElementSpans

/-!
# Frame の比較と三本矢の全単体図式の自然性

概要：Dwyer–Kan §7 の共通図式を元の source frame と終域の比較に自然にする。
方針：元の比較射を三本矢の縦射へ送り、全単体作用素への自然性を照合する。
規約：同じ augmentation・右脚・元の単体写像を保持する。
使われ方：既存の関手的置換と共通比較の選択独立性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.EInfinity.FrameHom

open CategoryTheory


variable {C : Type u} [Category.{v} C] (L R : MorphismProperty C)
  {X Y Z Z' : C} {A A' : SimplexCategory ⥤ C}
  (p : A ⟶ (Functor.const SimplexCategory).obj X)
  (p' : A' ⟶ (Functor.const SimplexCategory).obj X)
  (hp : ∀ n, L (p.app n)) (hp' : ∀ n, L (p'.app n))
  (j : Y ⟶ Z) (hj : R j)

/-- 概要：source frame の同じ比較は全単体の三本矢の自然変換（Dwyer–Kan §7）。
方針：比較射を左の縦射にし、元の augmentation との整合を使う。
規約：元の Hom の前合成による全単体の係数射を保持する。
使われ方：frame の共通比較を同じ三本矢の図式へ送る。 -/
def frameSpanSourceComparison (α : A' ⟶ A) (hα : α ≫ p = p') :
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Z).mapElements.op ⋙ frameElementSpanFunctor L R A' p' hp' j hj ⟶
      frameElementSpanFunctor L R A p hp j hj where
  app s :=
    { left := α.app s.unop.obj.unop
      right := 𝟙 Z
      left_w := NatTrans.congr_app hα s.unop.obj.unop
      middle_w := Category.comp_id _
      right_w := Category.comp_id _ }
  naturality s t f := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext
    · exact α.naturality f.unop.hom.unop
    · exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- 概要：終域の同じ比較は全単体の三本矢の自然変換（Dwyer–Kan §7）。
方針：比較射を右の縦射にし、右脚の元の可換三角形を使う。
規約：元の Hom の後合成による全単体の係数射を保持する。
使われ方：同じ fibrant 置換の比較と高次の共通図式の自然性。 -/
def frameSpanTargetComparison (j' : Y ⟶ Z') (hj' : R j') (β : Z ⟶ Z') (hβ : j ≫ β = j') :
    frameElementSpanFunctor L R A p hp j hj ⟶
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map β).mapElements.op ⋙ frameElementSpanFunctor L R A p hp j' hj' where
  app s :=
    { left := 𝟙 _
      right := β
      left_w := Category.id_comp _
      middle_w := (Category.id_comp _).symm
      right_w := hβ }
  naturality s t f := by
    apply _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.hom_ext
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · change (𝟙 Z) ≫ β = β ≫ 𝟙 Z'
      exact (Category.id_comp β).trans (Category.comp_id β).symm

end SerrePositivity.EInfinity.FrameHom
