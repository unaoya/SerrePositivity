module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorHomActions
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorFamily

/-!
# 元の正規化テンソル Hom と実 DK Hom の全二変数自然同型

概要：同じ点ごとの Hom 同型を、始域に反変・標的に共変な全自然同型へまとめる。
方針：実内部 Hom 関手と元の前後合成に対する全次数の等式を使う。
規約：元の Hom 複体・smart 切断・Γ の射を保つ。
使われ方：標準自由単位の前後作用と実 ∞ Hom 比較の整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.HomotopyFunctionComplex
variable (A : Type u) [CommRing A]

def normalizedTensorHomBifunctor : (Complex A)ᵒᵖ ⥤ Complex A ⥤ SSet.{u} :=
  (normalizedSimplexTensorFamily A).op ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor

def actualDoldKanHomBifunctor : (Complex A)ᵒᵖ ⥤ Complex A ⥤ SSet.{u} :=
  MonoidalClosed.internalHom ⋙
    (Functor.whiskeringRight (Complex A) (Complex A) SSet.{u}).obj (truncatedDoldKanFunctor A)

def normalizedTensorHomDoldKanIso :
    normalizedTensorHomBifunctor A ≅ actualDoldKanHomBifunctor A :=
  NatIso.ofComponents (fun X =>
    NatIso.ofComponents (fun Y => normalizedSimplexTensorHomIso A X.unop Y) (by
      intro Y Z g
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro f
      exact normalizedSimplexTensorHomEquiv_postcomp A X.unop n.unop f g)) (by
    intro X Y g
    apply NatTrans.ext
    funext Z
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    change normalizedSimplexTensorHomEquiv A Y.unop Z n.unop
      ((g.unop ▷ (BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n.unop)) ≫ f) =
      ((truncatedDoldKanFunctor A).map ((MonoidalClosed.pre g.unop).app Z)).app n
        (normalizedSimplexTensorHomEquiv A X.unop Z n.unop f)
    rw [internalHom_pre_eq]
    exact normalizedSimplexTensorHomEquiv_precomp A Z g.unop n.unop f)

lemma actualDoldKanHomBifunctor_obj (X Y : Complex A) :
    ((actualDoldKanHomBifunctor A).obj (Opposite.op X)).obj Y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace
        (R := A) (D := Complex A) X Y := rfl

lemma normalizedTensorHomDoldKanIso_hom_app (X Y : Complex A) :
    (((normalizedTensorHomDoldKanIso A).hom.app (Opposite.op X)).app Y) =
      (normalizedSimplexTensorHomIso A X Y).hom := rfl

lemma normalizedTensorHomDoldKanIso_inv_app (X Y : Complex A) :
    (((normalizedTensorHomDoldKanIso A).inv.app (Opposite.op X)).app Y) =
      (normalizedSimplexTensorHomIso A X Y).inv := rfl

end SerrePositivity.EInfinity.ComplexLimits
