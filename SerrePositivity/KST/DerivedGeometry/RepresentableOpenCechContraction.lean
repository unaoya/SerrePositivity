module

public import SerrePositivity.KST.DerivedGeometry.FormalCoproductCechFunctor
public import SerrePositivity.KST.DerivedGeometry.MaximalOpenCech
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.Types.Products

/-!
概要：被覆元に含まれる開からの表現可能関手による Čech の収縮。
方針：有限積の比較と像の終対象を使い、被覆元への射を追加退化にする。
規約：元の開の和集合が全体であるとは要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の自由 Čech 鎖複体。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w a b
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable {X : Type u} [TopologicalSpace X] {ι : Type w}
  (U : ι → Opens X) (V : Opens X) (hU : ∀ i, U i ≤ V)

/--
概要：像の増大先が終対象になると、増大 Čech は像の標準の増大 Čech と同型。
方針：全次数の積比較を使い、増大との両立は終対象の一意性から得る。
規約：元の開 V が終対象である必要はない。
使われ方：TT §3、Toën §3.2 の小さい開上の Čech 計算。
-/
def mappedBoundedOpenCechIso {D : Type a} [Category.{b} D] [HasFiniteProducts D]
    (F : Opens X ⥤ D) [PreservesFiniteProducts F] (hT : IsTerminal (F.obj V)) :
    ((SimplicialObject.Augmented.whiskering _ _).obj
      (formalCoproductMapFunctor F)).obj (boundedOpenCechAugmented U V hU) ≅
      (((formalCoproductMapFunctor F).obj (FormalCoproduct.mk ι U)).cech.augmentOfIsTerminal
        (FormalCoproduct.isTerminalIncl _ hT)) :=
  Comma.isoMk (formalCoproductCechFunctorIso F (FormalCoproduct.mk ι U)) (Iso.refl _)
    (by
      ext : 1
      apply (FormalCoproduct.isTerminalIncl _ hT).hom_ext)

/--
概要：W が被覆元に含まれると、W からの Hom で評価した Čech に追加退化がある。
方針：W から V への Hom は終対象となり、指定された被覆元への射を先頭に挿入する。
規約：単なる完全性の仮定でなく実際の追加退化を構成する。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech の局所収縮。
-/
def representableOpenCechExtraDegeneracy (W : Opens X) (j : ι) (hWj : W ≤ U j) :
    (((SimplicialObject.Augmented.whiskering _ _).obj
      (formalCoproductMapFunctor (coyoneda.obj (.op W)))).obj
        (boundedOpenCechAugmented U V hU)).ExtraDegeneracy := by
  let F := coyoneda.obj (.op W)
  let hT : IsTerminal (F.obj V) :=
    (Types.isTerminalEquivUnique _).symm
      { default := homOfLE (hWj.trans (hU j))
        uniq := fun _ => @Subsingleton.elim (W ⟶ V) inferInstance _ _ }
  let d : F.obj V ⟶ F.obj (U j) := ↾fun _ => homOfLE hWj
  exact .ofIso (mappedBoundedOpenCechIso U V hU F hT).symm
    (FormalCoproduct.extraDegeneracyCech
      ((formalCoproductMapFunctor F).obj (FormalCoproduct.mk ι U)) hT (i₀ := j) d)

end SerrePositivity.KST.DerivedGeometry
