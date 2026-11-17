module

public import SerrePositivity.HomologicalAlgebra.Cech.Composition

/-!
概要：B1の同じ二重環Čech図式を、元の基底上の環の射に自然にする。
方針：既存のArrowのconerveの射をUnderへ持ち上げ、既存の二変数テンソル関手で写す。
規約：元の増大項と全ての余面・退化を保ち、平坦性はここでは仮定しない。
使われ方：相対fppfの被覆変数を残した同じ二重Čech比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v w
set_option backward.isDefEq.respectTransparency false
variable {A : CommRingCat.{u}} {B C D : Under A}

/-- 同じ基底の恒等射と元の係数の射の四角形。 -/
def cechUnderArrowMap (f : B ⟶ C) : Arrow.mk B.hom ⟶ Arrow.mk C.hom :=
  Arrow.homMk (𝟙 A) f.right (by simpa using (Under.w f).symm)

/-- 元の四角形は恒等射を保つ。 -/
theorem cechUnderArrowMap_id (B : Under A) : cechUnderArrowMap (𝟙 B) = 𝟙 _ := by
  apply Arrow.hom_ext <;> rfl

/-- 元の四角形は合成を保つ。 -/
theorem cechUnderArrowMap_comp (f : B ⟶ C) (g : C ⟶ D) :
    cechUnderArrowMap (f ≫ g) = cechUnderArrowMap f ≫ cechUnderArrowMap g := by
  apply Arrow.hom_ext
  · simp [cechUnderArrowMap]
  · rfl

/-- B1の同じ増大conerveの、元の基底上の係数の射。 -/
def cechUnderConerveMap (f : B ⟶ C) :
    SerrePositivity.Cech.underCech B ⟶ SerrePositivity.Cech.underCech C where
  left := 𝟙 _
  right :=
    { app := fun n ↦ Under.homMk ((Arrow.mapCechConerve (cechUnderArrowMap f)).app n) (by
        change WidePushout.head _ ≫ WidePushout.desc _ _ _ = WidePushout.head _
        rw [WidePushout.head_desc]
        simp [cechUnderArrowMap])
      naturality := by
        intro m n σ
        apply StructuredArrow.hom_ext
        exact (Arrow.mapCechConerve (cechUnderArrowMap f)).naturality σ }
  w := by
    apply NatTrans.ext
    funext n
    exact (Under.mkIdInitial (X := A)).hom_ext _ _

/-- 同じ増大conerveの係数移送は恒等射を保つ。 -/
theorem cechUnderConerveMap_id (B : Under A) : cechUnderConerveMap (𝟙 B) = 𝟙 _ := by
  apply Comma.hom_ext
  · rfl
  · apply NatTrans.ext
    funext n
    apply StructuredArrow.hom_ext
    change ((CosimplicialObject.cechConerve.map (cechUnderArrowMap (𝟙 B))).app n) = _
    rw [cechUnderArrowMap_id]
    exact congr_app (CosimplicialObject.cechConerve.map_id (Arrow.mk B.hom)) n

/-- 同じ増大conerveの係数移送は合成を保つ。 -/
theorem cechUnderConerveMap_comp (f : B ⟶ C) (g : C ⟶ D) :
    cechUnderConerveMap (f ≫ g) = cechUnderConerveMap f ≫ cechUnderConerveMap g := by
  apply Comma.hom_ext
  · simp [cechUnderConerveMap]
  · apply NatTrans.ext
    funext n
    apply StructuredArrow.hom_ext
    change ((CosimplicialObject.cechConerve.map (cechUnderArrowMap (f ≫ g))).app n) = _
    rw [cechUnderArrowMap_comp, Functor.map_comp]
    rfl

/-- B1と同じ増大単体図式での係数移送。 -/
def cechUnderDiagramMap (f : B ⟶ C) :
    SerrePositivity.Cech.asDiagram B ⟶ SerrePositivity.Cech.asDiagram C :=
  AugmentedSimplexCategory.equivAugmentedCosimplicialObject.inverse.map (cechUnderConerveMap f)

/-- 同じ増大単体図式の係数移送は恒等射を保つ。 -/
theorem cechUnderDiagramMap_id (B : Under A) : cechUnderDiagramMap (𝟙 B) = 𝟙 _ := by
  simp [cechUnderDiagramMap, cechUnderConerveMap_id]

/-- 同じ増大単体図式の係数移送は合成を保つ。 -/
theorem cechUnderDiagramMap_comp (f : B ⟶ C) (g : C ⟶ D) :
    cechUnderDiagramMap (f ≫ g) = cechUnderDiagramMap f ≫ cechUnderDiagramMap g := by
  simp [cechUnderDiagramMap, cechUnderConerveMap_comp]

/-- B1の同じ項ごとのテンソル積の二重図式での係数移送。 -/
def cechTensorDiagramMap {B' C' : Under A} (f : B ⟶ B') (g : C ⟶ C') :
    SerrePositivity.Cech.tensorCech B C ⟶ SerrePositivity.Cech.tensorCech B' C' :=
  Functor.whiskerRight ((cechUnderDiagramMap f).prod (cechUnderDiagramMap g))
    (SerrePositivity.Cech.ringTensor A)

/-- 元の二重図式の係数移送は恒等射を保つ。 -/
theorem cechTensorDiagramMap_id (B C : Under A) :
    cechTensorDiagramMap (𝟙 B) (𝟙 C) = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  simp only [cechTensorDiagramMap, cechUnderDiagramMap_id,
    Functor.whiskerRight_app, NatTrans.prod, NatTrans.id_app]
  change (SerrePositivity.Cech.ringTensor A).map (𝟙 _) = 𝟙 _
  exact (SerrePositivity.Cech.ringTensor A).map_id _

/-- 元の二重図式の係数移送は合成を保つ。 -/
theorem cechTensorDiagramMap_comp {B' B'' C' C'' : Under A}
    (f : B ⟶ B') (f' : B' ⟶ B'') (g : C ⟶ C') (g' : C' ⟶ C'') :
    cechTensorDiagramMap (f ≫ f') (g ≫ g') =
      cechTensorDiagramMap f g ≫ cechTensorDiagramMap f' g' := by
  apply NatTrans.ext
  funext n
  simp [cechTensorDiagramMap, cechUnderDiagramMap_comp, NatTrans.prod, ← Functor.map_comp]

/-- 元の被覆変数を残したB1の同じ二重環Čech図式。 -/
def cechTensorDiagramFunctor {J : Type v} [Category.{w} J] (B C : J ⥤ Under A) :
    J ⥤ (AugmentedSimplexCategory × AugmentedSimplexCategory ⥤ CommRingCat.{u}) where
  obj j := SerrePositivity.Cech.tensorCech (B.obj j) (C.obj j)
  map f := cechTensorDiagramMap (B.map f) (C.map f)
  map_id j := by rw [B.map_id, C.map_id, cechTensorDiagramMap_id]
  map_comp f g := by rw [B.map_comp, C.map_comp, cechTensorDiagramMap_comp]

end SerrePositivity.AlgebraicGeometry
