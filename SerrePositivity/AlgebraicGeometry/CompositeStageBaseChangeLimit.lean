module

public import SerrePositivity.AlgebraicGeometry.StageBaseChangeLimit

/-!
概要：有限段で因子化した係数写像に沿う底変換図式の極限を、元の模型の頂点で取る。
方針：Over.map の下の連結極限を反映し、pullback と同型による cone の移送を使う。
規約：底変換・合成・極限の法則。遷移射の忠実平坦性は使わない。
使われ方：A07 の C03 に、選んだ閉イデアルの型を保ったまま渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J]

/-- ある段で因子化した係数写像に沿う、各後段への実際の底変換。 -/
def compositeStageBaseChangeDiagram (D : J ⥤ Scheme.{u}) (i : J)
    {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S) : Over i ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.map γ ⋙ Over.pullback p ⋙ Over.forget _

/-- 因子化した係数写像で、元の cone を底変換した cone。 -/
def compositeStageBaseChangeCone (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S) :
    Cone (compositeStageBaseChangeDiagram D i γ p) :=
  (Over.map γ ⋙ Over.pullback p ⋙ Over.forget _).mapCone ((Over.conePost D i).obj c)

attribute [local instance] IsCofiltered.isConnected

/-- 係数写像を合成してから底変換しても、実際の極限 cone を得る。 -/
def isLimit_compositeStageBaseChangeCone [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i : J)
    {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S) :
    IsLimit (compositeStageBaseChangeCone D c i γ p) := by
  have h : IsLimit ((Over.map γ).mapCone ((Over.conePost D i).obj c)) :=
    isLimitOfReflects (Over.forget S)
      (isLimitOfPreserves (Over.forget (D.obj i)) (Over.isLimitConePost i hc))
  exact isLimitOfPreserves (Over.pullback p ⋙ Over.forget _) h

/-- 元の底変換空間を、因子化した係数写像による cone の頂点と同型にする。 -/
def compositeStageBaseChangePointIso (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S) (g : c.pt ⟶ S)
    (h : c.π.app i ≫ γ = g) :
    pullback p g ≅ (compositeStageBaseChangeCone D c i γ p).pt :=
  pullbackSymmetry p g ≪≫ pullback.congrHom h.symm rfl

/-- 選んだ閉部分の元の底変換空間を頂点に保つ cone。 -/
def compositeStageBaseChangeConeWithPoint (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S) (g : c.pt ⟶ S)
    (h : c.π.app i ≫ γ = g) : Cone (compositeStageBaseChangeDiagram D i γ p) :=
  (compositeStageBaseChangeCone D c i γ p).extend
    (compositeStageBaseChangePointIso D c i γ p g h).hom

/-- 元の模型の頂点を保つ cone の実際の極限性。 -/
def isLimit_compositeStageBaseChangeConeWithPoint [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i : J)
    {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S) (g : c.pt ⟶ S)
    (h : c.π.app i ≫ γ = g) :
    IsLimit (compositeStageBaseChangeConeWithPoint D c i γ p g h) :=
  (isLimit_compositeStageBaseChangeCone D c hc i γ p).extendIso
    (compositeStageBaseChangePointIso D c i γ p g h).hom

set_option backward.isDefEq.respectTransparency false in
/-- 合成係数の底変換図式の遷移射は、元の遷移射の底変換。 -/
theorem isPullback_compositeStageBaseChangeDiagram_map
    (D : J ⥤ Scheme.{u}) (i : J) {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S)
    {j k : Over i} (f : j ⟶ k) :
    IsPullback ((compositeStageBaseChangeDiagram D i γ p).map f)
      (pullback.fst (D.map j.hom ≫ γ) p) (pullback.fst (D.map k.hom ≫ γ) p)
      (D.map f.left) := by
  apply IsPullback.flip
  apply IsPullback.of_bot ?_ (by simp [compositeStageBaseChangeDiagram])
    (IsPullback.of_hasPullback (D.map k.hom ≫ γ) p)
  have hw : D.map f.left ≫ (D.map k.hom ≫ γ) = D.map j.hom ≫ γ := by
    rw [← Category.assoc, ← D.map_comp, Over.w f]
  simpa [compositeStageBaseChangeDiagram, hw] using
    (IsPullback.of_hasPullback (D.map j.hom ≫ γ) p)

/-- affine な遷移射の、合成係数による底変換も affine。 -/
instance compositeStageBaseChangeDiagram_isAffineHom_map
    (D : J ⥤ Scheme.{u}) (i : J) {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S)
    [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)] {j k : Over i} (f : j ⟶ k) :
    IsAffineHom ((compositeStageBaseChangeDiagram D i γ p).map f) :=
  MorphismProperty.of_isPullback
    (isPullback_compositeStageBaseChangeDiagram_map D i γ p f).flip inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- 準コンパクトな射の合成係数による底変換図式の各段は準コンパクト。 -/
instance compositeStageBaseChangeDiagram_compactSpace
    (D : J ⥤ Scheme.{u}) (i : J) {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S)
    [∀ j, CompactSpace (D.obj j)] [QuasiCompact p] (j : Over i) :
    CompactSpace ((compositeStageBaseChangeDiagram D i γ p).obj j) := by
  change CompactSpace (pullback (D.map j.hom ≫ γ) p : Scheme.{u})
  haveI : QuasiCompact (pullback.fst (D.map j.hom ≫ γ) p) :=
    MorphismProperty.pullback_fst (D.map j.hom ≫ γ) p ‹QuasiCompact p›
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst (D.map j.hom ≫ γ) p)

set_option backward.isDefEq.respectTransparency false in
/-- 準分離な射の合成係数による底変換図式の各段は準分離。 -/
instance compositeStageBaseChangeDiagram_quasiSeparatedSpace
    (D : J ⥤ Scheme.{u}) (i : J) {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S)
    [∀ j, QuasiSeparatedSpace (D.obj j)] [QuasiSeparated p] (j : Over i) :
    QuasiSeparatedSpace ((compositeStageBaseChangeDiagram D i γ p).obj j) := by
  change QuasiSeparatedSpace (pullback (D.map j.hom ≫ γ) p : Scheme.{u})
  haveI : QuasiSeparated (pullback.fst (D.map j.hom ≫ γ) p) :=
    MorphismProperty.pullback_fst (D.map j.hom ≫ γ) p ‹QuasiSeparated p›
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map j.hom ≫ γ) p)

set_option backward.isDefEq.respectTransparency false in
/-- 元の模型の頂点を保つ cone の射影と、各段の第一射影の可換式。 -/
@[reassoc (attr := simp)]
theorem compositeStageBaseChangeConeWithPoint_π_fst
    (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S) (g : c.pt ⟶ S)
    (h : c.π.app i ≫ γ = g) (j : Over i) :
    (compositeStageBaseChangeConeWithPoint D c i γ p g h).π.app j ≫
        pullback.fst (D.map j.hom ≫ γ) p = pullback.snd p g ≫ c.π.app j.left := by
  simp [compositeStageBaseChangeConeWithPoint, compositeStageBaseChangeCone,
    compositeStageBaseChangePointIso, Cone.extend, Over.conePost, Over.pullback, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- 元の模型の頂点を保つ cone の射影と、周辺模型への第二射影の可換式。 -/
@[reassoc (attr := simp)]
theorem compositeStageBaseChangeConeWithPoint_π_snd
    (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S) (g : c.pt ⟶ S)
    (h : c.π.app i ≫ γ = g) (j : Over i) :
    (compositeStageBaseChangeConeWithPoint D c i γ p g h).π.app j ≫
        pullback.snd (D.map j.hom ≫ γ) p = pullback.fst p g := by
  simp [compositeStageBaseChangeConeWithPoint, compositeStageBaseChangeCone,
    compositeStageBaseChangePointIso, Cone.extend, Over.conePost, Over.pullback, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- 元の模型の頂点を保つ cone の各射影は、元の図式の射影の底変換。 -/
theorem isPullback_compositeStageBaseChangeConeWithPoint_π
    (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S) (g : c.pt ⟶ S)
    (h : c.π.app i ≫ γ = g) (j : Over i) :
    IsPullback ((compositeStageBaseChangeConeWithPoint D c i γ p g h).π.app j)
      (pullback.snd p g) (pullback.fst (D.map j.hom ≫ γ) p) (c.π.app j.left) := by
  apply IsPullback.flip
  apply IsPullback.of_bot ?_
    (compositeStageBaseChangeConeWithPoint_π_fst D c i γ p g h j).symm
    (IsPullback.of_hasPullback (D.map j.hom ≫ γ) p)
  rw [compositeStageBaseChangeConeWithPoint_π_snd, ← Category.assoc, c.w, h]
  exact (IsPullback.of_hasPullback p g).flip

end SerrePositivity.AlgebraicGeometry
