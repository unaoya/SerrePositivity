module

public import SerrePositivity.DifferentialGraded.Module.Hom.ColimitsAndRightHom
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# 同じ dg 加群のテンソルと全 Hom の随伴

概要：M10 の source frame へ、既存のパラメータ転置を実随伴として渡す。
方針：元の転置と逆転置の両逆・自然性を束ねる。
規約：HA §4.2.1、元の通常 Hom と全 Hom 複体を保持する。
使われ方：半自由加群の Hom の右 Quillen 条件からテンソルの左 Quillen 条件へ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：既存の転置は元の全ての標的加群射と可換。
方針：同じ主 Hom end の全評価で Hom 後合成の式を使う。
規約：HA §4.2.1、元の閉零射。使われ方：同じテンソル/Hom 随伴の自然性。 -/
lemma moduleParamCurry_postcompose {K : Complex A} {M N P : ModuleCategory A D}
    (f : moduleTensorLeftObj A D K M ⟶ N) (g : N ⟶ P) :
    moduleParamCurry A D (f ≫ g) =
      moduleParamCurry A D f ≫ eHomWhiskerLeft (Complex A) M g := by
  apply moduleHom_ext (M := ForgetEnrichment.to (Complex A) M)
    (N := ForgetEnrichment.to (Complex A) P)
  intro x
  let E := moduleEvaluation A D x
  let πN := moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) N) x
  let πP := moduleHomπ A D (ForgetEnrichment.to (Complex A) M)
    (ForgetEnrichment.to (Complex A) P) x
  calc
    _ = curryRight (E.map (f ≫ g)) := moduleParamCurry_π A D (f ≫ g) x
    _ = curryRight (E.map f ≫ E.map g) := congrArg curryRight (E.map_comp f g)
    _ = curryRight (E.map f) ≫ homPostcompose (E.obj M) (E.map g) :=
      curryRight_naturality_target (E.map f) (E.map g)
    _ = (moduleParamCurry A D f ≫ πN) ≫ homPostcompose (E.obj M) (E.map g) :=
      congrArg (fun z => z ≫ homPostcompose (E.obj M) (E.map g))
        (moduleParamCurry_π A D f x).symm
    _ = moduleParamCurry A D f ≫ (πN ≫ homPostcompose (E.obj M) (E.map g)) :=
      Category.assoc _ _ _
    _ = moduleParamCurry A D f ≫ (eHomWhiskerLeft (Complex A) M g ≫ πP) :=
      congrArg (fun z => moduleParamCurry A D f ≫ z)
        (moduleHomWhiskerLeft_π A D (M := M) g x).symm
    _ = _ := (Category.assoc _ _ _).symm

/-- 概要：同じテンソル加群からの射と主 Hom 複体への射は同値。
方針：既存の転置と逆転置の両逆を使う。
規約：HA §4.2.1、元の二つの Hom 集合。使われ方：実随伴の Hom 同値。 -/
def moduleTensorHomEquiv (M : ModuleCategory A D) (K : Complex A)
    (N : ModuleCategory A D) :
    ((tensorModuleFunctor (ForgetEnrichment.to (Complex A) M)).obj K ⟶ N) ≃
      (K ⟶ ((eHomFunctor (Complex A) (ModuleCategory A D)).obj (op M)).obj N) where
  toFun := moduleParamCurry A D
  invFun := moduleParamUncurry A D
  left_inv := moduleParamUncurry_curry A D
  right_inv := moduleParamCurry_uncurry A D

/-- 概要：元の固定加群のテンソルは同じ全 Hom 関手の左随伴。
方針：同じ転置の両変数自然性を実 Hom 同値に付ける。
規約：HA §4.2.1、随伴の存在を仮定しない。使われ方：具体的 source frame の移送。 -/
def moduleTensorHomAdjunction (M : ModuleCategory A D) :
    tensorModuleFunctor (ForgetEnrichment.to (Complex A) M) ⊣
      (eHomFunctor (Complex A) (ModuleCategory A D)).obj (op M) :=
  Adjunction.mkOfHomEquiv {
    homEquiv := moduleTensorHomEquiv A D M
    homEquiv_naturality_left_symm := fun f g =>
      (moduleParamUncurry_precomp A D f g).symm
    homEquiv_naturality_right := fun f g => moduleParamCurry_postcompose A D f g }

end SerrePositivity.EInfinity.Modules
