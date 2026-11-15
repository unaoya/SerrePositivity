module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
概要：固定した段への射を底変換する図式と、その実際の極限 cone。
方針：Over.post・Over.pullback と連結極限の保存を使う。
規約：既存の底変換・極限の法則。模型の存在は追加仮定にしない。
使われ方：A07 の有限段の閉部分模型に C03 を適用する周辺図式。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J]

/-- 固定した段への射の、元の図式の各後段への実際の底変換。 -/
def stageBaseChangeDiagram (D : J ⥤ Scheme.{u}) (i : J)
    {Y : Scheme.{u}} (p : Y ⟶ D.obj i) : Over i ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback p ⋙ Over.forget _

/-- 固定した段への射の、元の cone の頂点への実際の底変換。 -/
def stageBaseChangeCone (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {Y : Scheme.{u}} (p : Y ⟶ D.obj i) : Cone (stageBaseChangeDiagram D i p) :=
  (Over.pullback p ⋙ Over.forget _).mapCone ((Over.conePost D i).obj c)

attribute [local instance] IsCofiltered.isConnected

/-- 底変換した実際の cone は極限 cone。 -/
def isLimit_stageBaseChangeCone [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i : J)
    {Y : Scheme.{u}} (p : Y ⟶ D.obj i) : IsLimit (stageBaseChangeCone D c i p) :=
  isLimitOfPreserves (Over.pullback p ⋙ Over.forget _) (Over.isLimitConePost i hc)

set_option backward.isDefEq.respectTransparency false in
/-- 底変換図式の遷移射と第一射影の正方形は Cartesian。 -/
theorem isPullback_stageBaseChangeDiagram_map
    (D : J ⥤ Scheme.{u}) (i : J) {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    {j k : Over i} (f : j ⟶ k) :
    IsPullback ((stageBaseChangeDiagram D i p).map f)
      (pullback.fst (D.map j.hom) p) (pullback.fst (D.map k.hom) p) (D.map f.left) := by
  apply IsPullback.flip
  apply IsPullback.of_bot ?_ (by simp [stageBaseChangeDiagram])
    (IsPullback.of_hasPullback (D.map k.hom) p)
  simpa [stageBaseChangeDiagram, ← D.map_comp, Over.w f] using
    (IsPullback.of_hasPullback (D.map j.hom) p)

/-- affine な遷移射の底変換図式も affine な遷移射を持つ。 -/
instance stageBaseChangeDiagram_isAffineHom_map
    (D : J ⥤ Scheme.{u}) (i : J) {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((stageBaseChangeDiagram D i p).map f) :=
  MorphismProperty.of_isPullback (isPullback_stageBaseChangeDiagram_map D i p f).flip
    inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-- 準コンパクトな射の底変換図式の各段は準コンパクト。 -/
instance stageBaseChangeDiagram_compactSpace
    (D : J ⥤ Scheme.{u}) (i : J) {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    [∀ j, CompactSpace (D.obj j)] [QuasiCompact p] (j : Over i) :
    CompactSpace ((stageBaseChangeDiagram D i p).obj j) :=
by
  change CompactSpace (pullback (D.map j.hom) p : Scheme.{u})
  haveI : QuasiCompact (pullback.fst (D.map j.hom) p) :=
    MorphismProperty.pullback_fst (D.map j.hom) p ‹QuasiCompact p›
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map j.hom) p)

set_option backward.isDefEq.respectTransparency.types false in
/-- 準分離な射の底変換図式の各段は準分離。 -/
instance stageBaseChangeDiagram_quasiSeparatedSpace
    (D : J ⥤ Scheme.{u}) (i : J) {Y : Scheme.{u}} (p : Y ⟶ D.obj i)
    [∀ j, QuasiSeparatedSpace (D.obj j)] [QuasiSeparated p] (j : Over i) :
    QuasiSeparatedSpace ((stageBaseChangeDiagram D i p).obj j) :=
by
  change QuasiSeparatedSpace (pullback (D.map j.hom) p : Scheme.{u})
  haveI : QuasiSeparated (pullback.fst (D.map j.hom) p) :=
    MorphismProperty.pullback_fst (D.map j.hom) p ‹QuasiSeparated p›
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map j.hom) p)

end SerrePositivity.AlgebraicGeometry
