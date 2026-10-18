module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# 単体集合の片端を貼った mapping cylinder

概要：写像の mapping cylinder と、底への収縮の局所化可逆性を構成する。
方針：零端点の pushout と、端点の anodyne 性を使う。
規約：Segal 1974 Proposition 1.6 の骨格の通常の pushout と二重写像円筒の比較。
使われ方：片方の脚が単射の pushout への円筒の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.SimplicialModel
open scoped Simplicial

/--
概要：零端点に写像を貼った mapping cylinder。
方針：零端点と指定した写像の pushout を取る。
規約：一端点は後で別の対象を貼るために残す。
使われ方：二重写像円筒の二段階の pushout 表示。
-/
def mappingCylinder {C A : SSet.{u}} (f : C ⟶ A) : SSet.{u} :=
  pushout (SSet.ι₀ (X := C)) f

/--
概要：mapping cylinder への円筒の包含。
方針：pushout の第一の射を使う。
規約：始域は C と標準区間の積。
使われ方：残る端点と収縮の計算。
-/
def mappingCylinderTop {C A : SSet.{u}} (f : C ⟶ A) : C ⊗ Δ[1] ⟶ mappingCylinder f :=
  pushout.inl _ _

/--
概要：mapping cylinder への底の対象の包含。
方針：pushout の第二の射を使う。
規約：この包含は零端点の anodyne 性の pushout。
使われ方：底への収縮の可逆性。
-/
def mappingCylinderBase {C A : SSet.{u}} (f : C ⟶ A) : A ⟶ mappingCylinder f :=
  pushout.inr _ _

/--
概要：mapping cylinder のまだ貼り付けていない端点。
方針：一端点を円筒の包含へ合成する。
規約：始域は元の写像の始域。
使われ方：二重写像円筒への二つ目の付着。
-/
def mappingCylinderEndpoint {C A : SSet.{u}} (f : C ⟶ A) : C ⟶ mappingCylinder f :=
  SSet.ι₁ ≫ mappingCylinderTop f

/--
概要：mapping cylinder の底への収縮。
方針：円筒では第一射影の後で元の写像を使い、底では恒等射を使う。
規約：零端点の条件は標準円筒の第一射影の計算則。
使われ方：二重写像円筒から通常の pushout への比較。
-/
def mappingCylinderRetraction {C A : SSet.{u}} (f : C ⟶ A) : mappingCylinder f ⟶ A :=
  pushout.desc (fst C (Δ[1] : SSet.{u}) ≫ f) (𝟙 A) (by simp)

/--
概要：円筒の後の収縮は第一射影と元の写像の合成である。
方針：pushout の第一成分を計算する。
規約：標準区間の変数を忘れる。
使われ方：二重写像円筒の収縮との比較。
-/
@[reassoc] theorem mappingCylinderTop_retraction {C A : SSet.{u}} (f : C ⟶ A) :
    mappingCylinderTop f ≫ mappingCylinderRetraction f = fst C (Δ[1] : SSet.{u}) ≫ f :=
  pushout.inl_desc ..

/--
概要：底の包含の後の収縮は恒等射である。
方針：pushout からの desc の第二成分を計算する。
規約：底を固定する収縮。
使われ方：収縮の局所化可逆性の二対三。
-/
@[reassoc] theorem mappingCylinderBase_retraction {C A : SSet.{u}} (f : C ⟶ A) :
    mappingCylinderBase f ≫ mappingCylinderRetraction f = 𝟙 A := pushout.inr_desc ..

/--
概要：残る端点の後の収縮は元の写像である。
方針：円筒側の desc と一端点の第一射影を計算する。
規約：二つ目の付着との可換性。
使われ方：通常の pushout への比較射の構成。
-/
@[reassoc] theorem mappingCylinderEndpoint_retraction {C A : SSet.{u}} (f : C ⟶ A) :
    mappingCylinderEndpoint f ≫ mappingCylinderRetraction f = f := by
  rw [mappingCylinderEndpoint, Category.assoc]
  change SSet.ι₁ ≫ (pushout.inl _ _ ≫ pushout.desc _ _ _) = f
  rw [pushout.inl_desc, ← Category.assoc, SSet.ι₁_fst, Category.id_comp]

/--
概要：mapping cylinder の底の包含は anodyne である。
方針：零端点の anodyne 性を pushout へ移す。
規約：元の写像には単射性を要求しない。
使われ方：収縮の局所化可逆性。
-/
theorem mappingCylinderBase_anodyne {C A : SSet.{u}} (f : C ⟶ A) :
    SSet.anodyneExtensions (mappingCylinderBase f) :=
  SSet.anodyneExtensions.of_isPushout (IsPushout.of_hasPushout (SSet.ι₀ (X := C)) f).flip
    (AnodyneHomotopy.endpoint_zero_anodyne C)

/--
概要：mapping cylinder の底への収縮は局所化同型である。
方針：anodyne な底の包含との合成が恒等であることを使う。
規約：始域・終域の Kan 性は不要。
使われ方：単射な脚を共有する pushout の比較。
-/
theorem mappingCylinderRetraction_localized_isIso {C A : SSet.{u}} (f : C ⟶ A) :
    IsIso (AnodyneHomotopy.anodyneQ.map (mappingCylinderRetraction f)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have := Localization.inverts Q SSet.anodyneExtensions _ (mappingCylinderBase_anodyne f)
  have h : IsIso (Q.map (mappingCylinderBase f) ≫ Q.map (mappingCylinderRetraction f)) := by
    rw [← Q.map_comp, mappingCylinderBase_retraction]
    infer_instance
  exact (isIso_comp_left_iff _ _).mp h

end SerrePositivity.KST.Comparison
