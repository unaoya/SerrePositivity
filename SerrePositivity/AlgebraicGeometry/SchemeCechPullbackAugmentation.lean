module

public import SerrePositivity.AlgebraicGeometry.SchemeCechPreimage
public import SerrePositivity.AlgebraicGeometry.OpenCoverCechAugmentation

/-!
概要：実際の Čech 引き戻しを、大域切断からの増大写像に自然にする。
方針：係数の射、逆像被覆の比較、その合成の順に零次で照合する。
規約：係数環と加群の宇宙を分け、既存の引き戻しの射を保持する。
使われ方：閉中心を持つ射影四角形の増大写像の被覆比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u v
variable {X Y : Scheme.{u}} {R : Type v} [CommRing R]
variable {ι : Type} [LinearOrder ι]

set_option backward.isDefEq.respectTransparency false in
/-- 係数前層の実際の射は、大域切断からの増大写像を保つ。 -/
theorem schemeCechCoefficientMap_augmentation
    {P P' : (Y.Opens)ᵒᵖ ⥤ ModuleCat.{u} R} (η : P ⟶ P') (U : ι → Y.Opens) :
    ((fullCechComplexMap (openCoverCechCoefficientMap η U)).f 0).hom.comp
        (openCoverCechAugmentation P U) =
      (openCoverCechAugmentation P' U).comp (η.app (op ⊤)).hom := by
  apply LinearMap.ext
  intro x
  funext t
  change ((η.app (op (cechOpenIntersection U (cechTupleSupport t)))).hom
    ((P.map (homOfLE (show cechOpenIntersection U (cechTupleSupport t) ≤ ⊤
      from le_top)).op).hom x)) = _
  exact congrArg (fun m ↦ m.hom x) (η.naturality
    (homOfLE (show cechOpenIntersection U (cechTupleSupport t) ≤ ⊤ from le_top)).op)

set_option backward.isDefEq.respectTransparency false in
/-- 逆像被覆の既存の比較は、同じ全空間の切断からの増大写像を保つ。 -/
theorem schemeCechPreimageComplexIso_augmentation
    (f : X ⟶ Y) (Q : (X.Opens)ᵒᵖ ⥤ ModuleCat.{u} R) (U : ι → Y.Opens) :
    ((schemeCechPreimageComplexIso f Q U).hom.f 0).hom.comp
        (openCoverCechAugmentation ((Opens.map f.base).op ⋙ Q) U) =
      openCoverCechAugmentation Q (fun i ↦ f ⁻¹ᵁ U i) := by
  apply LinearMap.ext
  intro x
  funext t
  change (Q.map _).hom ((Q.map _).hom x) = (Q.map _).hom x
  change (Q.map _ ≫ Q.map _).hom x = (Q.map _).hom x
  rw [← Q.map_comp]
  congr 2

set_option backward.isDefEq.respectTransparency false in
/-- 実際の Čech 引き戻しの零次は、係数の全空間の成分で増大写像と可換。 -/
theorem schemeCechPullbackMap_augmentation
    (f : X ⟶ Y) (Q : (X.Opens)ᵒᵖ ⥤ ModuleCat.{u} R)
    {P : (Y.Opens)ᵒᵖ ⥤ ModuleCat.{u} R}
    (η : P ⟶ (Opens.map f.base).op ⋙ Q) (U : ι → Y.Opens) :
    ((schemeCechPullbackMap f Q η U).f 0).hom.comp (openCoverCechAugmentation P U) =
      (openCoverCechAugmentation Q (fun i ↦ f ⁻¹ᵁ U i)).comp (η.app (op ⊤)).hom := by
  change (((schemeCechPreimageComplexIso f Q U).hom.f 0).hom.comp
    ((fullCechComplexMap (openCoverCechCoefficientMap η U)).f 0).hom).comp _ = _
  rw [LinearMap.comp_assoc, schemeCechCoefficientMap_augmentation,
    ← LinearMap.comp_assoc, schemeCechPreimageComplexIso_augmentation]

end SerrePositivity.AlgebraicGeometry
