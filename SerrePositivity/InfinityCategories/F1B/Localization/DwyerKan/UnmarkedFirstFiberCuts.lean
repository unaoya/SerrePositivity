module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordActionCutComparison
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedFirstGeneratorImage

/-!
# 元の最小非指定列の像の切断の接頭射と残り

概要：最初の非指定列を含む fiber の前後の射列から圧縮後の切断を回収する。
方針：最小性による前置区間の指定性を元の固定切断の比較に代入する。
規約：元の端点移送・同じ生成矢・全射列を保持する。
使われ方：prefix・残りの元の全語の余極限での像の一致。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFiber
open CategoryTheory SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} (f : a ⟶ b) (S : Zigzag W.paths a X Y)
  (h : ∃ i, column W S i ≠ [])

lemma image_forward : b.direction (f.orderHom (firstColumn W S h)) = .forward :=
  (f.direction_eq _).trans (firstColumn_forward W S h)

def prefixMap := WordActionCut.prefixMap W f S (f.orderHom (firstColumn W S h))
  (firstColumn W S h) rfl (image_forward W f S h)

def residualMap := WordActionCut.residual W f S (f.orderHom (firstColumn W S h))
  (firstColumn W S h) rfl (image_forward W f S h)

lemma prefixMap_mem : W.paths (prefixMap W f S h) :=
  WordActionCut.prefix_mem W f S (f.orderHom (firstColumn W S h)) (firstColumn W S h)
    rfl (image_forward W f S h) (fun k _ hk => before_firstColumn_mem W S h k hk)

variable {g : Quiver.Total C} (P : FixedCut W g (S.arrow (firstColumn W S h)))
  (Q : FixedCut W g ((WordAction.obj f S).arrow (f.orderHom (firstColumn W S h))))

lemma cut_left : HEq Q.left ((prefixMap W f S h).comp P.left) :=
  WordActionCut.cut_left W f S (f.orderHom (firstColumn W S h)) (firstColumn W S h)
    rfl (image_forward W f S h) (fun k _ hk => before_firstColumn_mem W S h k hk) P Q

lemma cut_right : HEq Q.right (P.right.comp (residualMap W f S h)) :=
  WordActionCut.cut_right W f S (f.orderHom (firstColumn W S h)) (firstColumn W S h)
    rfl (image_forward W f S h) (fun k _ hk => before_firstColumn_mem W S h k hk) P Q

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFiber
