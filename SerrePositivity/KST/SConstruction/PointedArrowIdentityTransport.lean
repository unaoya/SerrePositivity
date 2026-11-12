module
public import SerrePositivity.KST.SConstruction.AssemblyArrowIdentityLegs
public import SerrePositivity.KST.SConstruction.PointedChoiceBaseIso
public import SerrePositivity.KST.SConstruction.PointedExtensionArrowDiagram
public import SerrePositivity.KST.SConstruction.PointedLiftArrowDiagram

/-! # 恒等成分の比較と入力の両端移送
概要：恒等成分を元の選択空間へ戻した後の移送は、射図式の二つの脚と一致する。
方針：選択空間の写像空間への射影で比較し、恒等入力の表示の違いを除く。
規約：同じパラメーターを全次数で厳密に移送する。
使われ方：coherent な cospan の二脚を元の因子の自然性の両端へ同定する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra.PointedMapping

/-- 延長図式の恒等成分を元の点ごとの延長選択へ戻す同型。 -/
def pointedExtensionArrowIdentityIso {I : Type v} [Category.{w} I]
    {R A L : I ⥤ PointedSimplicialSet.{u}} (η : R ⟶ A) (θ : R ⟶ L) (X : I) :
    pointedExtensionArrowSpace η θ (assemblyArrowMk (𝟙 X)) ≅
      pointedExtensionSpace (η.app X) (θ.app X) :=
  pointedExtensionBaseIso (η.app X) (h := R.map (𝟙 X) ≫ θ.app X) (h' := θ.app X)
    (by rw [R.map_id, Category.id_comp])

/-- 点ごとの源の延長を指定入力射で後合成して混合空間へ移す。 -/
def pointedExtensionSourceTransport {I : Type v} [Category.{w} I]
    {R A L : I ⥤ PointedSimplicialSet.{u}} (η : R ⟶ A) (θ : R ⟶ L)
    {X Y : I} (f : X ⟶ Y) :
    pointedExtensionSpace (η.app X) (θ.app X) ⟶
      pointedExtensionArrowSpace η θ (assemblyArrowMk f) :=
  pointedExtensionTransport (η.app X) (θ.app X) (η.app X) (R.map f ≫ θ.app Y)
    (𝟙 (R.obj X)) (𝟙 (A.obj X)) (L.map f) (by simp)
    (by rw [Category.id_comp]; exact (θ.naturality f).symm)

/-- 点ごとの標的の延長を指定入力射で前合成して混合空間へ移す。 -/
def pointedExtensionTargetTransport {I : Type v} [Category.{w} I]
    {R A L : I ⥤ PointedSimplicialSet.{u}} (η : R ⟶ A) (θ : R ⟶ L)
    {X Y : I} (f : X ⟶ Y) :
    pointedExtensionSpace (η.app Y) (θ.app Y) ⟶
      pointedExtensionArrowSpace η θ (assemblyArrowMk f) :=
  pointedExtensionTransport (η.app Y) (θ.app Y) (η.app X) (R.map f ≫ θ.app Y)
    (R.map f) (A.map f) (𝟙 (L.obj Y)) (η.naturality f) (by simp)

/-- 源の恒等成分の比較と元の後合成は、射図式の源側の脚そのもの。 -/
lemma pointedExtensionArrowIdentityIso_source {I : Type v} [Category.{w} I]
    {R A L : I ⥤ PointedSimplicialSet.{u}} (η : R ⟶ A) (θ : R ⟶ L)
    {X Y : I} (f : X ⟶ Y) :
    (pointedExtensionArrowIdentityIso η θ X).hom ≫ pointedExtensionSourceTransport η θ f =
      pointedExtensionArrowMap η θ (assemblyArrowFromSource f) := by
  let ps := pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app X) (L.obj X)).right
    (SSet.yonedaEquiv.symm (familyVertex (θ.app X)))
  let px := pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app X) (L.obj X)).right
    (SSet.yonedaEquiv.symm (familyVertex (R.map (𝟙 X) ≫ θ.app X)))
  let pm := pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app X) (L.obj Y)).right
    (SSet.yonedaEquiv.symm (familyVertex (R.map f ≫ θ.app Y)))
  have hs : pointedExtensionSourceTransport η θ f ≫ pm =
      ps ≫ pointedMappingTransport (𝟙 (A.obj X)) (L.map f) :=
    pointedExtensionTransport_projection (η.app X) (θ.app X) (η.app X)
      (R.map f ≫ θ.app Y) (𝟙 _) (𝟙 _) (L.map f) (by simp)
      (by rw [Category.id_comp]; exact (θ.naturality f).symm)
  have hb : (pointedExtensionArrowIdentityIso η θ X).hom ≫ ps = px :=
    pointedExtensionBaseIso_projection (η.app X)
      (show R.map (𝟙 X) ≫ θ.app X = θ.app X by rw [R.map_id, Category.id_comp])
  have hm : pointedExtensionArrowMap η θ (assemblyArrowFromSource f) ≫ pm =
      px ≫ pointedMappingTransport (A.map (𝟙 X)) (L.map f) :=
    pointedExtensionTransport_projection (η.app X) (R.map (𝟙 X) ≫ θ.app X)
      (η.app X) (R.map f ≫ θ.app Y) (R.map (𝟙 X)) (A.map (𝟙 X)) (L.map f)
      (η.naturality (𝟙 X)) (pointedExtensionArrow_restriction θ (assemblyArrowFromSource f))
  rw [A.map_id] at hm
  apply pullback.hom_ext
  · change ((pointedExtensionArrowIdentityIso η θ X).hom ≫
      pointedExtensionSourceTransport η θ f) ≫ pm =
        pointedExtensionArrowMap η θ (assemblyArrowFromSource f) ≫ pm
    rw [Category.assoc, hs, ← Category.assoc, hb]
    exact hm.symm
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 標的の恒等成分の比較と元の前合成は、射図式の標的側の脚そのもの。 -/
lemma pointedExtensionArrowIdentityIso_target {I : Type v} [Category.{w} I]
    {R A L : I ⥤ PointedSimplicialSet.{u}} (η : R ⟶ A) (θ : R ⟶ L)
    {X Y : I} (f : X ⟶ Y) :
    (pointedExtensionArrowIdentityIso η θ Y).hom ≫ pointedExtensionTargetTransport η θ f =
      pointedExtensionArrowMap η θ (assemblyArrowFromTarget f) := by
  let ps := pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app Y) (L.obj Y)).right
    (SSet.yonedaEquiv.symm (familyVertex (θ.app Y)))
  let px := pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app Y) (L.obj Y)).right
    (SSet.yonedaEquiv.symm (familyVertex (R.map (𝟙 Y) ≫ θ.app Y)))
  let pm := pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (η.app X) (L.obj Y)).right
    (SSet.yonedaEquiv.symm (familyVertex (R.map f ≫ θ.app Y)))
  have hs : pointedExtensionTargetTransport η θ f ≫ pm =
      ps ≫ pointedMappingTransport (A.map f) (𝟙 (L.obj Y)) :=
    pointedExtensionTransport_projection (η.app Y) (θ.app Y) (η.app X)
      (R.map f ≫ θ.app Y) (R.map f) (A.map f) (𝟙 _) (η.naturality f) (by simp)
  have hb : (pointedExtensionArrowIdentityIso η θ Y).hom ≫ ps = px :=
    pointedExtensionBaseIso_projection (η.app Y)
      (show R.map (𝟙 Y) ≫ θ.app Y = θ.app Y by rw [R.map_id, Category.id_comp])
  have hm : pointedExtensionArrowMap η θ (assemblyArrowFromTarget f) ≫ pm =
      px ≫ pointedMappingTransport (A.map f) (L.map (𝟙 Y)) :=
    pointedExtensionTransport_projection (η.app Y) (R.map (𝟙 Y) ≫ θ.app Y)
      (η.app X) (R.map f ≫ θ.app Y) (R.map f) (A.map f) (L.map (𝟙 Y))
      (η.naturality f) (pointedExtensionArrow_restriction θ (assemblyArrowFromTarget f))
  rw [L.map_id] at hm
  apply pullback.hom_ext
  · change ((pointedExtensionArrowIdentityIso η θ Y).hom ≫
      pointedExtensionTargetTransport η θ f) ≫ pm =
        pointedExtensionArrowMap η θ (assemblyArrowFromTarget f) ≫ pm
    rw [Category.assoc, hs, ← Category.assoc, hb]
    exact hm.symm
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 持ち上げ図式の恒等成分を元の切断選択へ戻す同型。 -/
def pointedLiftArrowIdentityIso {I : Type v} [Category.{w} I]
    {E B : I ⥤ PointedSimplicialSet.{u}} (p : E ⟶ B) (X : I) :
    pointedLiftArrowSpace p (assemblyArrowMk (𝟙 X)) ≅ pointedLiftSpace (p.app X) (𝟙 (B.obj X)) :=
  pointedLiftBaseIso (p.app X) (b := B.map (𝟙 X)) (b' := 𝟙 (B.obj X)) (B.map_id X)

/-- 点ごとの源の切断を指定入力射で後合成して混合空間へ移す。 -/
def pointedLiftSourceTransport {I : Type v} [Category.{w} I]
    {E B : I ⥤ PointedSimplicialSet.{u}} (p : E ⟶ B) {X Y : I} (f : X ⟶ Y) :
    pointedLiftSpace (p.app X) (𝟙 (B.obj X)) ⟶ pointedLiftArrowSpace p (assemblyArrowMk f) :=
  pointedLiftTransport (p.app X) (𝟙 (B.obj X)) (p.app Y) (B.map f)
    (𝟙 (B.obj X)) (E.map f) (B.map f) (p.naturality f) (by simp)

/-- 点ごとの標的の切断を指定入力射で前合成して混合空間へ移す。 -/
def pointedLiftTargetTransport {I : Type v} [Category.{w} I]
    {E B : I ⥤ PointedSimplicialSet.{u}} (p : E ⟶ B) {X Y : I} (f : X ⟶ Y) :
    pointedLiftSpace (p.app Y) (𝟙 (B.obj Y)) ⟶ pointedLiftArrowSpace p (assemblyArrowMk f) :=
  pointedLiftTransport (p.app Y) (𝟙 (B.obj Y)) (p.app Y) (B.map f)
    (B.map f) (𝟙 (E.obj Y)) (𝟙 (B.obj Y)) (by simp) (by simp)

/-- 源の恒等成分の比較と元の切断の後合成は、射図式の源側の脚そのもの。 -/
lemma pointedLiftArrowIdentityIso_source {I : Type v} [Category.{w} I]
    {E B : I ⥤ PointedSimplicialSet.{u}} (p : E ⟶ B) {X Y : I} (f : X ⟶ Y) :
    (pointedLiftArrowIdentityIso p X).hom ≫ pointedLiftSourceTransport p f =
      pointedLiftArrowMap p (assemblyArrowFromSource f) := by
  let ps := pullback.fst (PointedObject.basedHomMap (B.obj X) (p.app X)).right
    (SSet.yonedaEquiv.symm (familyVertex (𝟙 (B.obj X))))
  let px := pullback.fst (PointedObject.basedHomMap (B.obj X) (p.app X)).right
    (SSet.yonedaEquiv.symm (familyVertex (B.map (𝟙 X))))
  let pm := pullback.fst (PointedObject.basedHomMap (B.obj X) (p.app Y)).right
    (SSet.yonedaEquiv.symm (familyVertex (B.map f)))
  have hs : pointedLiftSourceTransport p f ≫ pm =
      ps ≫ pointedMappingTransport (𝟙 (B.obj X)) (E.map f) :=
    pointedLiftTransport_projection (p.app X) (𝟙 _) (p.app Y) (B.map f)
      (𝟙 _) (E.map f) (B.map f) (p.naturality f) (by simp)
  have hb : (pointedLiftArrowIdentityIso p X).hom ≫ ps = px :=
    pointedLiftBaseIso_projection (p.app X) (B.map_id X)
  have hm : pointedLiftArrowMap p (assemblyArrowFromSource f) ≫ pm =
      px ≫ pointedMappingTransport (B.map (𝟙 X)) (E.map f) :=
    pointedLiftTransport_projection (p.app X) (B.map (𝟙 X)) (p.app Y) (B.map f)
      (B.map (𝟙 X)) (E.map f) (B.map f) (p.naturality f)
      (pointedLiftArrow_base B (assemblyArrowFromSource f))
  have ht : pointedMappingTransport (B.map (𝟙 X)) (E.map f) =
      pointedMappingTransport (𝟙 (B.obj X)) (E.map f) :=
    congrArg (fun a : B.obj X ⟶ B.obj X => pointedMappingTransport a (E.map f)) (B.map_id X)
  rw [ht] at hm
  apply pullback.hom_ext
  · change ((pointedLiftArrowIdentityIso p X).hom ≫ pointedLiftSourceTransport p f) ≫ pm =
        pointedLiftArrowMap p (assemblyArrowFromSource f) ≫ pm
    rw [Category.assoc, hs, ← Category.assoc, hb]
    exact hm.symm
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 標的の恒等成分の比較と元の切断の前合成は、射図式の標的側の脚そのもの。 -/
lemma pointedLiftArrowIdentityIso_target {I : Type v} [Category.{w} I]
    {E B : I ⥤ PointedSimplicialSet.{u}} (p : E ⟶ B) {X Y : I} (f : X ⟶ Y) :
    (pointedLiftArrowIdentityIso p Y).hom ≫ pointedLiftTargetTransport p f =
      pointedLiftArrowMap p (assemblyArrowFromTarget f) := by
  let ps := pullback.fst (PointedObject.basedHomMap (B.obj Y) (p.app Y)).right
    (SSet.yonedaEquiv.symm (familyVertex (𝟙 (B.obj Y))))
  let px := pullback.fst (PointedObject.basedHomMap (B.obj Y) (p.app Y)).right
    (SSet.yonedaEquiv.symm (familyVertex (B.map (𝟙 Y))))
  let pm := pullback.fst (PointedObject.basedHomMap (B.obj X) (p.app Y)).right
    (SSet.yonedaEquiv.symm (familyVertex (B.map f)))
  have hs : pointedLiftTargetTransport p f ≫ pm =
      ps ≫ pointedMappingTransport (B.map f) (𝟙 (E.obj Y)) :=
    pointedLiftTransport_projection (p.app Y) (𝟙 _) (p.app Y) (B.map f)
      (B.map f) (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hb : (pointedLiftArrowIdentityIso p Y).hom ≫ ps = px :=
    pointedLiftBaseIso_projection (p.app Y) (B.map_id Y)
  have hm : pointedLiftArrowMap p (assemblyArrowFromTarget f) ≫ pm =
      px ≫ pointedMappingTransport (B.map f) (E.map (𝟙 Y)) :=
    pointedLiftTransport_projection (p.app Y) (B.map (𝟙 Y)) (p.app Y) (B.map f)
      (B.map f) (E.map (𝟙 Y)) (B.map (𝟙 Y)) (p.naturality (𝟙 Y))
      (pointedLiftArrow_base B (assemblyArrowFromTarget f))
  rw [E.map_id] at hm
  apply pullback.hom_ext
  · change ((pointedLiftArrowIdentityIso p Y).hom ≫ pointedLiftTargetTransport p f) ≫ pm =
        pointedLiftArrowMap p (assemblyArrowFromTarget f) ≫ pm
    rw [Category.assoc, hs, ← Category.assoc, hb]
    exact hm.symm
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

end SerrePositivity.KST.SConstruction
