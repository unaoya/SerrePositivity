module

public import SerrePositivity.AlgebraicGeometry.StageModelOverLimit

/-!
概要：実際の固有模型を各段へ引き、固定した平坦射をさらに引く図式とその極限。
方針：Over の模型の極限から係数移送と pullback を合成し、元の被覆空間を頂点に保つ。
規約：底変換・極限・可換式の法則。q 自体に固有性は要求しない。
使われ方：A07 の平坦側の全射性と因子化を有限段へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J]

/-- 各基底の段の模型 T_j に、固定した射 q:Z→Y を引く実際の図式。 -/
def flatStageModelDiagram (D : J ⥤ Scheme.{u}) (i : J)
    {T Y Z : Scheme.{u}} (r : T ⟶ D.obj i) (β : T ⟶ Y) (q : Z ⟶ Y) :
    Over i ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback r ⋙ Over.map β ⋙ Over.pullback q ⋙ Over.forget _

/-- 元の模型の Over の cone を、係数移送と pullback で運ぶ。 -/
def flatStageModelCone (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {X T Y Z : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) (β : T ⟶ Y) (q : Z ⟶ Y) :
    Cone (flatStageModelDiagram D i r β q) :=
  (Over.map β ⋙ Over.pullback q ⋙ Over.forget _).mapCone
    (stageModelOverCone D c i a x r hpb)

attribute [local instance] IsCofiltered.isConnected

/-- 平坦側の実際の底変換図式の cone の極限性。 -/
def isLimit_flatStageModelCone [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i : J)
    {X T Y Z : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) (β : T ⟶ Y) (q : Z ⟶ Y) :
    IsLimit (flatStageModelCone D c i a x r hpb β q) := by
  have h : IsLimit ((Over.map β).mapCone (stageModelOverCone D c i a x r hpb)) :=
    isLimitOfReflects (Over.forget Y)
      (isLimitOfPreserves (Over.forget T) (isLimit_stageModelOverCone D c hc i a x r hpb))
  exact isLimitOfPreserves (Over.pullback q ⋙ Over.forget _) h

/-- 元の被覆空間を、係数移送した cone の頂点にする比較同型。 -/
def flatStageModelPointIso (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {X T Y Z : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) (β : T ⟶ Y) (q : Z ⟶ Y)
    (b : X ⟶ Y) (hb : a ≫ β = b) :
    pullback q b ≅ (flatStageModelCone D c i a x r hpb β q).pt :=
  pullbackSymmetry q b ≪≫ pullback.congrHom hb.symm rfl

/-- 元の被覆空間 pullback q b を頂点に保つ実際の cone。 -/
def flatStageModelConeWithPoint (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {X T Y Z : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) (β : T ⟶ Y) (q : Z ⟶ Y)
    (b : X ⟶ Y) (hb : a ≫ β = b) : Cone (flatStageModelDiagram D i r β q) :=
  (flatStageModelCone D c i a x r hpb β q).extend
    (flatStageModelPointIso D c i a x r hpb β q b hb).hom

/-- 元の被覆空間を頂点に保つ cone は実際の極限 cone。 -/
def isLimit_flatStageModelConeWithPoint [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i : J)
    {X T Y Z : Scheme.{u}} (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) (β : T ⟶ Y) (q : Z ⟶ Y)
    (b : X ⟶ Y) (hb : a ≫ β = b) :
    IsLimit (flatStageModelConeWithPoint D c i a x r hpb β q b hb) :=
  (isLimit_flatStageModelCone D c hc i a x r hpb β q).extendIso
    (flatStageModelPointIso D c i a x r hpb β q b hb).hom

/-- 各段の被覆空間から模型 T_j への実際の射。 -/
@[simps]
def flatStageModelProjection (D : J ⥤ Scheme.{u}) (i : J)
    {T Y Z : Scheme.{u}} (r : T ⟶ D.obj i) (β : T ⟶ Y) (q : Z ⟶ Y) :
    flatStageModelDiagram D i r β q ⟶ stageBaseChangeDiagram D i r where
  app j := pullback.fst (pullback.snd (D.map j.hom) r ≫ β) q
  naturality j k f := by simp [flatStageModelDiagram, stageBaseChangeDiagram, Over.pullback]

/-- 各段の射 q_j の遷移の正方形は Cartesian。 -/
theorem isPullback_flatStageModelDiagram_map
    (D : J ⥤ Scheme.{u}) (i : J) {T Y Z : Scheme.{u}}
    (r : T ⟶ D.obj i) (β : T ⟶ Y) (q : Z ⟶ Y) {j k : Over i} (f : j ⟶ k) :
    IsPullback ((flatStageModelDiagram D i r β q).map f)
      ((flatStageModelProjection D i r β q).app j)
      ((flatStageModelProjection D i r β q).app k) ((stageBaseChangeDiagram D i r).map f) := by
  have hw : (stageBaseChangeDiagram D i r).map f ≫
      (pullback.snd (D.map k.hom) r ≫ β) = pullback.snd (D.map j.hom) r ≫ β := by
    simp [stageBaseChangeDiagram, Over.pullback, Category.assoc]
  apply IsPullback.flip
  apply IsPullback.of_bot ?_ ((flatStageModelProjection D i r β q).naturality f).symm
    (IsPullback.of_hasPullback (pullback.snd (D.map k.hom) r ≫ β) q)
  simpa [flatStageModelDiagram, flatStageModelProjection, hw] using
    (IsPullback.of_hasPullback (pullback.snd (D.map j.hom) r ≫ β) q)

/-- 被覆空間の cone の射影と、模型の cone の射影の可換式。 -/
@[reassoc (attr := simp)]
theorem flatStageModelConeWithPoint_π_fst
    (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J) {X T Y Z : Scheme.{u}}
    (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) (β : T ⟶ Y) (q : Z ⟶ Y)
    (b : X ⟶ Y) (hb : a ≫ β = b) (j : Over i) :
    (flatStageModelConeWithPoint D c i a x r hpb β q b hb).π.app j ≫
        (flatStageModelProjection D i r β q).app j =
      pullback.snd q b ≫ (stageModelCone D c i a x r hpb).π.app j := by
  simp [flatStageModelConeWithPoint, flatStageModelCone, flatStageModelPointIso,
    flatStageModelProjection, stageModelCone, Cone.extend, Over.pullback, Category.assoc]

/-- 被覆空間の cone の射影と、固定した Z への射影の可換式。 -/
@[reassoc (attr := simp)]
theorem flatStageModelConeWithPoint_π_snd
    (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J) {X T Y Z : Scheme.{u}}
    (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) (β : T ⟶ Y) (q : Z ⟶ Y)
    (b : X ⟶ Y) (hb : a ≫ β = b) (j : Over i) :
    (flatStageModelConeWithPoint D c i a x r hpb β q b hb).π.app j ≫
        pullback.snd (pullback.snd (D.map j.hom) r ≫ β) q = pullback.fst q b := by
  simp [flatStageModelConeWithPoint, flatStageModelCone, flatStageModelPointIso,
    Cone.extend, Over.pullback, Category.assoc]

/-- 各極限射影と被覆空間の構造射の正方形は Cartesian。 -/
theorem isPullback_flatStageModelConeWithPoint_π
    (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J) {X T Y Z : Scheme.{u}}
    (a : X ⟶ T) (x : X ⟶ c.pt) (r : T ⟶ D.obj i)
    (hpb : IsPullback a x r (c.π.app i)) (β : T ⟶ Y) (q : Z ⟶ Y)
    (b : X ⟶ Y) (hb : a ≫ β = b) (j : Over i) :
    IsPullback ((flatStageModelConeWithPoint D c i a x r hpb β q b hb).π.app j)
      (pullback.snd q b) ((flatStageModelProjection D i r β q).app j)
      ((stageModelCone D c i a x r hpb).π.app j) := by
  have hw : (stageModelCone D c i a x r hpb).π.app j ≫
      (pullback.snd (D.map j.hom) r ≫ β) = b := by
    rw [← Category.assoc, stageModelCone_π_snd, hb]
  apply IsPullback.flip
  apply IsPullback.of_bot ?_ (flatStageModelConeWithPoint_π_fst D c i a x r hpb β q b hb j).symm
    (IsPullback.of_hasPullback (pullback.snd (D.map j.hom) r ≫ β) q)
  rw [flatStageModelConeWithPoint_π_snd, hw]
  exact (IsPullback.of_hasPullback q b).flip

end SerrePositivity.AlgebraicGeometry
