module

public import SerrePositivity.AlgebraicGeometry.FlatStageModelLimit

/-!
概要：実際の模型の図式を、元の基底 S の上の図式として扱う。
方針：二つの pullback の射影を合成し、元の cone の基底への可換式を保持する。
規約：合成・自然性・基底への係数移送の法則。
使われ方：A07 の元の X への S 上の因子化。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J]

/-- 模型 T_j の図式を元の基底 S の上へ送る。 -/
def stageModelBaseMap (D : J ⥤ Scheme.{u}) (i : J) {T S : Scheme.{u}}
    (r : T ⟶ D.obj i) (t : D ⟶ (Functor.const J).obj S) :
    stageBaseChangeDiagram D i r ⟶ (Functor.const (Over i)).obj S where
  app j := pullback.fst (D.map j.hom) r ≫ t.app j.left
  naturality j k f := by
    rw [← Category.assoc, (isPullback_stageBaseChangeDiagram_map D i r f).w,
      Category.assoc, t.naturality f.left]
    simp

/-- 被覆空間 W_j の図式を元の基底 S の上へ送る。 -/
def flatStageModelBaseMap (D : J ⥤ Scheme.{u}) (i : J) {T Y Z S : Scheme.{u}}
    (r : T ⟶ D.obj i) (β : T ⟶ Y) (q : Z ⟶ Y)
    (t : D ⟶ (Functor.const J).obj S) :
    flatStageModelDiagram D i r β q ⟶ (Functor.const (Over i)).obj S :=
  flatStageModelProjection D i r β q ≫ stageModelBaseMap D i r t

/-- 元の被覆の cone の射影と、元の基底 S への構造射は可換。 -/
theorem flatStageModelConeWithPoint_π_base
    (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J) {X T Y Z S : Scheme.{u}}
    (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) (β : T ⟶ Y) (q : Z ⟶ Y)
    (b : X ⟶ Y) (hb : a ≫ β = b) (t : D ⟶ (Functor.const J).obj S)
    (s : c.pt ⟶ S) (hs : ∀ j, c.π.app j ≫ t.app j = s) (j : Over i) :
    (flatStageModelConeWithPoint D c i a x r hpb β q b hb).π.app j ≫
        (flatStageModelBaseMap D i r β q t).app j = pullback.snd q b ≫ x ≫ s := by
  change (flatStageModelConeWithPoint D c i a x r hpb β q b hb).π.app j ≫
    (flatStageModelProjection D i r β q).app j ≫ pullback.fst (D.map j.hom) r ≫ t.app j.left = _
  rw [flatStageModelConeWithPoint_π_fst_assoc, stageModelCone_π_fst_assoc, hs]

end SerrePositivity.AlgebraicGeometry
