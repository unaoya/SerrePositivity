module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramFrameArrowCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictDiagramPointFrameEnd

/-!
概要：Hom要素圏上の指定錐の通常の極限性を、元のframe Homのend表示で証明する。
方針：恒等射への制限でwedgeを作り、各射の始点と終点からの分解を使う。
規約：通常の極限性だけであり、導来極限への比較の弱同値性とは区別する。
使われ方：HTT 4.2.4.4のRR02(a)、実比較の極限側の同定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits SSet
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- Hom要素圏の恒等射の対象。 -/
def strictDiagramArrowIdentity (d : StrictDiagramDirection)
    (j : AsSmall.{u} (strictDiagramIndex d)) : StrictDiagramArrowElements.{u} d :=
  { obj := (Opposite.op j, j), val := 𝟙 j }

/-- 指定射の始点の恒等射からの分解。 -/
def strictDiagramArrowFromSource {d : StrictDiagramDirection}
    (t : StrictDiagramArrowElements.{u} d) :
    strictDiagramArrowIdentity d t.obj.1.unop ⟶ t where
  hom := (𝟙 _, t.val)
  map_val := by change (𝟙 _ ≫ 𝟙 _) ≫ t.val = t.val; simp

/-- 指定射の終点の恒等射からの分解。 -/
def strictDiagramArrowFromTarget {d : StrictDiagramDirection}
    (t : StrictDiagramArrowElements.{u} d) :
    strictDiagramArrowIdentity d t.obj.2 ⟶ t where
  hom := (t.val.op, 𝟙 _)
  map_val := by change (t.val ≫ 𝟙 _) ≫ 𝟙 _ = t.val; simp

variable (A : Type u) [CommRing A] (d : StrictDiagramDirection)
  (X Y : StrictComplexDiagram A d)
local instance arrowLimitModel : HomotopicalAlgebra.ModelCategory (StrictComplexDiagram A d) :=
  strictDiagramReedyModelCategory A d

/-- 錐の恒等射成分を使う、元の二変数frame Hom上のwedge。 -/
def strictDiagramFrameArrowWedge (s : Cone (strictDiagramFrameArrowDiagram A d X Y)) :
    Wedge (strictDiagramPointFrameMapping A d X Y) :=
  Wedge.mk s.pt (fun j => s.π.app (strictDiagramArrowIdentity d (AsSmall.up.obj j))) (by
    intro i j a
    let t : StrictDiagramArrowElements.{u} d :=
      { obj := (Opposite.op (AsSmall.up.obj i), AsSmall.up.obj j), val := AsSmall.up.map a }
    have h₁ := s.w (strictDiagramArrowFromSource t)
    have h₂ := s.w (strictDiagramArrowFromTarget t)
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    have h := congrArg (fun k => k.app n z) (h₁.trans h₂.symm)
    change (((strictDiagramSourceFrame A d X).obj.obj n.unop).map (𝟙 i) ≫ (s.π.app (strictDiagramArrowIdentity d (AsSmall.up.obj i))).app n z) ≫
        (strictDiagramFibrantTarget A d Y).map a =
      (((strictDiagramSourceFrame A d X).obj.obj n.unop).map a ≫
        (s.π.app (strictDiagramArrowIdentity d (AsSmall.up.obj j))).app n z) ≫ (strictDiagramFibrantTarget A d Y).map (𝟙 j) at h
    change (s.π.app (strictDiagramArrowIdentity d (AsSmall.up.obj i))).app n z ≫
        (strictDiagramFibrantTarget A d Y).map a =
      ((strictDiagramSourceFrame A d X).obj.obj n.unop).map a ≫
        (s.π.app (strictDiagramArrowIdentity d (AsSmall.up.obj j))).app n z
    rw [(strictDiagramFibrantTarget A d Y).map_id j] at h
    simp only [CategoryTheory.Functor.op_obj, Opposite.unop_op,
      CategoryTheory.Functor.map_id, Category.id_comp] at h
    exact h.trans (Category.comp_id _))

/-- 全恒等射成分から復元した、同じframe Homへの写像。 -/
def strictDiagramFrameArrowLift (s : Cone (strictDiagramFrameArrowDiagram A d X Y)) :
    s.pt ⟶ strictDiagramFrameMapping A d X Y :=
  strictDiagramPointFrameEndLift A d X Y (strictDiagramFrameArrowWedge A d X Y s)

/-- 復元した写像は、恒等射だけでなく全ての添字射で元の錐を保つ。 -/
lemma strictDiagramFrameArrowLift_fac (s : Cone (strictDiagramFrameArrowDiagram A d X Y))
    (t : StrictDiagramArrowElements.{u} d) :
    strictDiagramFrameArrowLift A d X Y s ≫ strictDiagramFrameArrowLeg A d X Y t = s.π.app t := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  have h := congrArg (fun k => k.app n z) (s.w (strictDiagramArrowFromTarget t))
  change (((strictDiagramSourceFrame A d X).obj.obj n.unop).map (AsSmall.down.map t.val) ≫
      (s.π.app (strictDiagramArrowIdentity d t.obj.2)).app n z) ≫ (strictDiagramFibrantTarget A d Y).map (𝟙 _) = _ at h
  change ((strictDiagramSourceFrame A d X).obj.obj n.unop).map (AsSmall.down.map t.val) ≫
      (s.π.app (strictDiagramArrowIdentity d t.obj.2)).app n z = (s.π.app t).app n z
  dsimp only [strictDiagramArrowElementsBase, strictDiagramEndIndexFunctor,
    strictDiagramArrowIdentity, strictDiagramEvaluatedSourceFrames] at h ⊢
  simp only [CategoryTheory.Functor.op_obj, Opposite.unop_op,
    CategoryTheory.Functor.map_id, Category.comp_id] at h
  convert h using 1 <;> rfl

/-- 元の全自然変換のframe Homは、指定したHom要素圏上の錐の通常の極限である。 -/
def strictDiagramFrameArrowIsLimit : IsLimit (strictDiagramFrameArrowCone A d X Y) where
  lift := strictDiagramFrameArrowLift A d X Y
  fac := strictDiagramFrameArrowLift_fac A d X Y
  uniq s m hm := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    apply NatTrans.ext
    funext j
    have h := congrArg (fun k => k.app n z)
      (hm (strictDiagramArrowIdentity d (AsSmall.up.obj j)))
    change ((strictDiagramSourceFrame A d X).obj.obj n.unop).map (𝟙 j) ≫ (m.app n z).app j = _ at h
    change (m.app n z).app j =
      (s.π.app (strictDiagramArrowIdentity d (AsSmall.up.obj j))).app n z
    simp only [CategoryTheory.Functor.op_obj, Opposite.unop_op,
      CategoryTheory.Functor.map_id, Category.id_comp] at h
    convert h using 1 <;> rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
