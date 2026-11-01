module

public import SerrePositivity.InfinityCategories.ModelBridge.ForwardPathModelPropagation
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SegmentMapNaturality

/-!
# 元の zigzag の forward 区間への同時置換の代入

概要：元の区間の射列に、同じ元の端点への射・端点からの射による置換を代入する。
方針：元の Segment.chain と端点の等式を使い、縦射の元の正方形を comma の射へ移す。
規約：区間の全頂点・元の端点・全縦射の移送を保持する。長さ零も含む。
使われ方：backward 列の関手的分解を元の左右の forward ブロックに伝える。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ForwardPath
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : Word} {X Y : C}
  (p q : Fin (w.length + 1)) (hpq : p ≤ q)
  (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .forward)

def terminalBlockInput (S : Zigzag W w X Y) {E : C} (e : E ⟶ S.vertex q) :
    TerminalReplacement C (q.val - p.val) where
  left := E
  right := Segment.chain .forward S p q hpq hd
  hom := e ≫ eqToHom (congrArg S.vertex (Segment.index_last p q hpq).symm)

def initialBlockInput (S : Zigzag W w X Y) {E : C} (e : S.vertex p ⟶ E) :
    InitialReplacement C (q.val - p.val) where
  left := Segment.chain .forward S p q hpq hd
  right := E
  hom := eqToHom (congrArg S.vertex (Segment.index_zero p q hpq)) ≫ e

def terminalBlockComparison {S T : Zigzag W w X Y} (f : Zigzag.Hom S T)
    {E E' : C} (e : E ⟶ S.vertex q) (e' : E' ⟶ T.vertex q) (g : E ⟶ E')
    (h : e ≫ f.app q = g ≫ e') :
    terminalBlockInput p q hpq hd S e ⟶ terminalBlockInput p q hpq hd T e' where
  left := g
  right := Segment.forwardChainHom f p q hpq hd
  w := by
    change g ≫ (e' ≫ eqToHom (congrArg T.vertex (Segment.index_last p q hpq).symm)) =
      (e ≫ eqToHom (congrArg S.vertex (Segment.index_last p q hpq).symm)) ≫
        f.app (Segment.index p q hpq (Fin.last _))
    symm
    rw [Category.assoc, Segment.point_transport f (Segment.index_last p q hpq).symm,
      ← Category.assoc e, h, Category.assoc]

def initialBlockComparison {S T : Zigzag W w X Y} (f : Zigzag.Hom S T)
    {E E' : C} (e : S.vertex p ⟶ E) (e' : T.vertex p ⟶ E') (g : E ⟶ E')
    (h : f.app p ≫ e' = e ≫ g) :
    initialBlockInput p q hpq hd S e ⟶ initialBlockInput p q hpq hd T e' where
  left := Segment.forwardChainHom f p q hpq hd
  right := g
  w := by
    change f.app (Segment.index p q hpq 0) ≫
      (eqToHom (congrArg T.vertex (Segment.index_zero p q hpq)) ≫ e') =
        (eqToHom (congrArg S.vertex (Segment.index_zero p q hpq)) ≫ e) ≫ g
    rw [← Category.assoc, ← Segment.point_transport f (Segment.index_zero p q hpq),
      Category.assoc, h, ← Category.assoc]

section Model
variable [ModelCategory C]

lemma terminalBlockInput_trivialFibration (S : Zigzag W w X Y) {E : C}
    (e : E ⟶ S.vertex q) (he : trivialFibrations C e) :
    trivialFibrations C (terminalBlockInput p q hpq hd S e).hom :=
  (trivialFibrations C).comp_mem _ _ he ((trivialFibrations C).of_isIso _)

lemma initialBlockInput_trivialCofibration (S : Zigzag W w X Y) {E : C}
    (e : S.vertex p ⟶ E) (he : trivialCofibrations C e) :
    trivialCofibrations C (initialBlockInput p q hpq hd S e).hom :=
  (trivialCofibrations C).comp_mem _ _ ((trivialCofibrations C).of_isIso _) he

lemma terminalBlockComparison_weakEquivalence
    {S T : Zigzag (weakEquivalences C) w X Y} (f : Zigzag.Hom S T)
    {E E' : C} (e : E ⟶ S.vertex q) (e' : E' ⟶ T.vertex q) (g : E ⟶ E')
    (h : e ≫ f.app q = g ≫ e') (he : trivialFibrations C e) (he' : trivialFibrations C e')
    (i : Fin (q.val - p.val + 1)) :
    weakEquivalences C ((pullbackComparison (terminalBlockComparison p q hpq hd f e e' g h)).app
      i) :=
  pullbackComparison_weakEquivalence _ (terminalBlockInput_trivialFibration p q hpq hd S e he)
    (terminalBlockInput_trivialFibration p q hpq hd T e' he')
    (fun i => f.app_mem (Segment.index p q hpq i)) i

lemma initialBlockComparison_weakEquivalence
    {S T : Zigzag (weakEquivalences C) w X Y} (f : Zigzag.Hom S T)
    {E E' : C} (e : S.vertex p ⟶ E) (e' : T.vertex p ⟶ E') (g : E ⟶ E')
    (h : f.app p ≫ e' = e ≫ g) (he : trivialCofibrations C e) (he' : trivialCofibrations C e')
    (i : Fin (q.val - p.val + 1)) :
    weakEquivalences C ((pushoutComparison (initialBlockComparison p q hpq hd f e e' g h)).app
      i) :=
  pushoutComparison_weakEquivalence _ (initialBlockInput_trivialCofibration p q hpq hd S e he)
    (initialBlockInput_trivialCofibration p q hpq hd T e' he')
    (fun i => f.app_mem (Segment.index p q hpq i)) i

end Model
end SerrePositivity.EInfinity.Hammock.ForwardPath
