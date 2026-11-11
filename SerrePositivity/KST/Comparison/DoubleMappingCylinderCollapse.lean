module

public import SerrePositivity.KST.Comparison.MappingCylinderDouble
public import SerrePositivity.KST.Comparison.LocalizedPushoutCube

/-!
# 単射な脚を持つ pushout への二重写像円筒の比較

概要：片方の脚が単射なら、二重写像円筒を潰す通常の pushout への射は局所化同型である。
方針：片端の mapping cylinder の収縮を、共通の単射な脚の pushout の比較へ適用する。
規約：Segal 1974 Proposition 1.6 の有限骨格の付着との比較。
使われ方：Lemma 1.7 を通常の骨格の pushout へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped _root_.Simplicial
open SerrePositivity.SimplicialModel

/--
概要：二重写像円筒を通常の pushout へ潰す射。
方針：中央では区間を忘れ、左右では pushout の包含を使う。
規約：単射性を使わない実際の比較写像。
使われ方：片方の脚が単射のときの局所化同型。
-/
def doubleMappingCylinderCollapse {C A B : SSet.{u}} (f : C ⟶ A) (g : C ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder f g ⟶ pushout f g :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinderDesc f g (fst C (Δ[1] : SSet.{u}) ≫ f ≫ pushout.inl f g)
    (pushout.inl f g) (pushout.inr f g) (by simp)
    (by rw [← Category.assoc, ← Category.assoc, SSet.ι₁_fst, Category.id_comp, pushout.condition])

/--
概要：円筒を潰す比較の中央の円筒への制限。
方針：二重写像円筒の desc の第一成分を計算する。
規約：区間を忘れた後で元の左の射を使う。
使われ方：片端の収縮との比較。
-/
@[reassoc] theorem doubleMappingCylinder_middle_collapse {C A B : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_middle f g ≫ doubleMappingCylinderCollapse f g =
      fst C (Δ[1] : SSet.{u}) ≫ f ≫ pushout.inl f g :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_middle_desc ..

/--
概要：円筒を潰す比較は左の対象の包含を保つ。
方針：二重写像円筒の desc の計算則を使う。
規約：通常の pushout の第一の包含へ送る。
使われ方：pushout の比較との三角形。
-/
@[reassoc] theorem doubleMappingCylinder_left_collapse {C A B : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_left f g ≫ doubleMappingCylinderCollapse f g = pushout.inl f g :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_left_desc ..

/--
概要：円筒を潰す比較は右の対象の包含を保つ。
方針：二重写像円筒の desc の計算則を使う。
規約：通常の pushout の第二の包含へ送る。
使われ方：pushout の比較との三角形。
-/
@[reassoc] theorem doubleMappingCylinder_right_collapse {C A B : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f g ≫ doubleMappingCylinderCollapse f g = pushout.inr f g :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.doubleMappingCylinder_right_desc ..

/--
概要：片端の mapping cylinder からの比較と収縮は通常の pushout 上で一致する。
方針：片端の pushout の二成分で計算する。
規約：収縮の後に左の対象の包含を合成する。
使われ方：共通の単射な脚の pushout の比較。
-/
@[reassoc] theorem mappingCylinderToDouble_collapse {C A B : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) :
    mappingCylinderToDouble f g ≫ doubleMappingCylinderCollapse f g =
      mappingCylinderRetraction f ≫ pushout.inl f g := by
  apply pushout.hom_ext
  · change mappingCylinderTop f ≫ (mappingCylinderToDouble f g ≫
      doubleMappingCylinderCollapse f g) =
        mappingCylinderTop f ≫ (mappingCylinderRetraction f ≫ pushout.inl f g)
    rw [← Category.assoc, mappingCylinderTop_toDouble, doubleMappingCylinder_middle_collapse]
    rw [mappingCylinderTop_retraction_assoc]
  · change mappingCylinderBase f ≫ (mappingCylinderToDouble f g ≫
      doubleMappingCylinderCollapse f g) =
        mappingCylinderBase f ≫ (mappingCylinderRetraction f ≫ pushout.inl f g)
    rw [← Category.assoc, mappingCylinderBase_toDouble, doubleMappingCylinder_left_collapse]
    rw [← Category.assoc, mappingCylinderBase_retraction, Category.id_comp]

/--
概要：右の脚が単射なら、二重写像円筒の通常の pushout への比較は局所化同型である。
方針：片端の収縮の局所化可逆性を、右の脚を共通の単射とする pushout の比較へ移す。
規約：左の脚には単射性も Kan 性も要求しない。
使われ方：有限骨格の境界に沿う通常の付着への Lemma 1.7 の移送。
-/
theorem doubleMappingCylinderCollapse_localized_isIso {C A B : SSet.{u}}
    (f : C ⟶ A) (g : C ⟶ B) [Mono g] :
    IsIso (AnodyneHomotopy.anodyneQ.map (doubleMappingCylinderCollapse f g)) := by
  let r := mappingCylinderRetraction f
  have hr : IsIso (AnodyneHomotopy.anodyneQ.map r) := mappingCylinderRetraction_localized_isIso f
  have he : mappingCylinderEndpoint f ≫ r = f := mappingCylinderEndpoint_retraction f
  let hD := (mappingCylinderToDouble_isPushout f g).flip
  let hP := (IsPushout.of_hasPushout f g).flip
  let eD := hD.isoPushout
  let eP := hP.isoPushout
  let m := pushout.map g (mappingCylinderEndpoint f) g f (𝟙 B) r (𝟙 C)
    (by simp) (by simpa using he)
  have hm : IsIso (AnodyneHomotopy.anodyneQ.map m) :=
    pushoutMap_localized_isIso g (mappingCylinderEndpoint f) g f (𝟙 C) (𝟙 B) r
      (by infer_instance) (by infer_instance) hr (by simp) (by simpa using he)
  have hmL : pushout.inl g (mappingCylinderEndpoint f) ≫ m = pushout.inl g f := by simp [m]
  have hmR : pushout.inr g (mappingCylinderEndpoint f) ≫ m = r ≫ pushout.inr g f :=
    pushout.inr_desc ..
  have hPB : pushout.inr f g ≫ eP.hom = pushout.inl g f := hP.inl_isoPushout_hom
  have hPA : pushout.inl f g ≫ eP.hom = pushout.inr g f := hP.inr_isoPushout_hom
  have hDB : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.doubleMappingCylinder_right f g ≫ eD.hom =
      pushout.inl g (mappingCylinderEndpoint f) := hD.inl_isoPushout_hom
  have hDC : mappingCylinderToDouble f g ≫ eD.hom =
      pushout.inr g (mappingCylinderEndpoint f) := hD.inr_isoPushout_hom
  have hc : doubleMappingCylinderCollapse f g ≫ eP.hom = eD.hom ≫ m := by
    apply hD.hom_ext
    · simp only [← Category.assoc, doubleMappingCylinder_right_collapse,
        hPB, hDB, hmL]
    · rw [← Category.assoc, mappingCylinderToDouble_collapse,
        Category.assoc, hPA,
        ← Category.assoc, hDC, hmR]
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have h : IsIso (Q.map (doubleMappingCylinderCollapse f g) ≫ Q.map eP.hom) := by
    rw [← Q.map_comp, hc, Q.map_comp]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp h

end SerrePositivity.KST.Comparison
