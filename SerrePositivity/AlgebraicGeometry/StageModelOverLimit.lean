module

public import SerrePositivity.AlgebraicGeometry.StageBaseChangeLimit

/-!
概要：模型の実際の Cartesian な比較から、元の空間を頂点に保つ Over の極限 cone を作る。
方針：pullback の比較同型を Over の同型にし、既存の底変換の cone を同型で移す。
規約：底変換・極限・係数移送の法則。忠実平坦性は要求しない。
使われ方：A07 の平坦模型の図式を Over の底変換でさらに運ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J]

set_option backward.isDefEq.respectTransparency false in
/-- 実際の模型の Cartesian な比較を、Over の cone の頂点との同型にする。 -/
def stageModelOverPointIso (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {X T : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) :
    Over.mk a ≅ ((Over.pullback r).mapCone ((Over.conePost D i).obj c)).pt :=
  Over.isoMk (hpb.isoPullback ≪≫ pullbackSymmetry r (c.π.app i)) (by simp [Over.conePost, Category.assoc])

/-- 元の模型の写像 a:X→T を頂点に保つ、Over T の実際の cone。 -/
def stageModelOverCone (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {X T : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) : Cone (Over.post D ⋙ Over.pullback r) :=
  ((Over.pullback r).mapCone ((Over.conePost D i).obj c)).extend
    (stageModelOverPointIso D c i a x r hpb).hom

/-- 元の模型を頂点に保つ Over の cone の構造射は、元の a そのもの。 -/
@[simp]
theorem stageModelOverCone_pt_hom (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {X T : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) :
    (stageModelOverCone D c i a x r hpb).pt.hom = a := rfl

/-- 元の模型を頂点に保った Over の cone の実際の極限性。 -/
def isLimit_stageModelOverCone [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i : J)
    {X T : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) :
    IsLimit (stageModelOverCone D c i a x r hpb) :=
  (isLimitOfPreserves (Over.pullback r) (Over.isLimitConePost i hc)).extendIso
    (stageModelOverPointIso D c i a x r hpb).hom

/-- Over の cone を忘れ、元の X を頂点に持つ実際のスキームの cone にする。 -/
def stageModelCone (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {X T : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) : Cone (stageBaseChangeDiagram D i r) :=
  (Over.forget T).mapCone (stageModelOverCone D c i a x r hpb)

attribute [local instance] IsCofiltered.isConnected

/-- 元の X を頂点に持つ底変換図式の cone の極限性。 -/
def isLimit_stageModelCone [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i : J)
    {X T : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) :
    IsLimit (stageModelCone D c i a x r hpb) :=
  isLimitOfPreserves (Over.forget T) (isLimit_stageModelOverCone D c hc i a x r hpb)

set_option backward.isDefEq.respectTransparency false in
/-- 元の模型を頂点に保つ cone の、模型 T への射影の可換式。 -/
@[reassoc (attr := simp)]
theorem stageModelCone_π_snd (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {X T : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) (j : Over i) :
    (stageModelCone D c i a x r hpb).π.app j ≫ pullback.snd (D.map j.hom) r = a :=
  Over.w ((stageModelOverCone D c i a x r hpb).π.app j)

set_option backward.isDefEq.respectTransparency false in
/-- 元の模型を頂点に保つ cone の、元の基底の段への射影の可換式。 -/
@[reassoc (attr := simp)]
theorem stageModelCone_π_fst (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {X T : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) (j : Over i) :
    (stageModelCone D c i a x r hpb).π.app j ≫ pullback.fst (D.map j.hom) r =
      x ≫ c.π.app j.left := by
  simp [stageModelCone, stageModelOverCone, stageModelOverPointIso,
    Cone.extend, Over.conePost, Over.pullback, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- 元の模型の各射影は、元の図式の射影の実際の底変換。 -/
theorem isPullback_stageModelCone_π (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {X T : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) (j : Over i) :
    IsPullback ((stageModelCone D c i a x r hpb).π.app j) x
      (pullback.fst (D.map j.hom) r) (c.π.app j.left) := by
  apply IsPullback.flip
  apply IsPullback.of_bot ?_ (stageModelCone_π_fst D c i a x r hpb j).symm
    (IsPullback.of_hasPullback (D.map j.hom) r)
  rw [stageModelCone_π_snd, c.w]
  exact hpb.flip

end SerrePositivity.AlgebraicGeometry
