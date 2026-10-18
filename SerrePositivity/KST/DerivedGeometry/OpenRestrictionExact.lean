module

public import SerrePositivity.KST.DerivedGeometry.CoefficientModuleRestriction

/-!
概要：係数加群層の開制限の余極限保存と完全性。
方針：基礎加法群の層への忘却で余極限を判定し、開集合の随伴を使う。
規約：係数の平坦性を要求しない。
使われ方：TT 3.19・8.1、Toën §3.2 の非有界導来制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry

/--
概要：基礎加法群の層の開制限は左随伴。
方針：開包含の像と逆像の随伴を層へ移す。
規約：同じ開部分への制限関手を使う。
使われ方：TT 3.19・8.1 の開制限の余極限保存。
-/
instance openAddSheafRestriction_isLeftAdjoint {X : Scheme.{u}} (U : X.Opens) :
    (U.sheafRestrict (C := AddCommGrpCat.{u})).IsLeftAdjoint := by
  let : U.isOpenEmbedding.isOpenMap.functor.IsContinuous
      (Opens.grothendieckTopology U) (Opens.grothendieckTopology X) :=
    U.isOpenEmbedding.functor_isContinuous
  let : (Opens.map (Opens.inclusion' (X := (X : TopCat)) U)).IsContinuous
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology U) :=
    instIsContinuousOpensCarrierMapGrothendieckTopology (Opens.inclusion' U)
  let adj : U.isOpenEmbedding.functor ⊣ Opens.map (Opens.inclusion' (X := (X : TopCat)) U) := by
    exact U.isOpenEmbedding.isOpenMap.adjunction
  exact (adj.sheafPushforwardContinuous
    (Opens.grothendieckTopology U) (Opens.grothendieckTopology X)).isLeftAdjoint

namespace CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X) (U : X.Opens)

/--
概要：係数加群層の開制限を忘れた層は基礎加法群の層の開制限。
方針：同じ切断と制限写像の恒等同型を束ねる。
規約：係数環層の比較は恒等射のまま。
使われ方：TT 3.19・8.1 の余極限保存の判定。
-/
def openRestrictionToSheafIso :
    B.openRestriction U ⋙ SheafOfModules.toSheaf (B.restrict U).ring ≅
      SheafOfModules.toSheaf B.ring ⋙ U.sheafRestrict (C := AddCommGrpCat.{u}) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/--
概要：係数加群層の開制限は小さい余極限を保つ。
方針：基礎加法群の層への忘却の余極限反映と開制限の左随伴性を使う。
規約：開ごとの切断関手の完全性は仮定しない。
使われ方：TT 3.19・8.1、Toën §3.2 の導来制限。
-/
instance openRestriction_preservesColimits :
    PreservesColimitsOfSize.{u,u} (B.openRestriction U) := by
  let G := SheafOfModules.toSheaf (B.restrict U).ring
  have : PreservesColimitsOfSize.{u,u} G := toSheaf_preservesColimits _
  have : G.ReflectsIsomorphisms :=
    PresheafOfModules.instReflectsIsomorphismsSheafOfModulesSheafAddCommGrpCatToSheaf_1
  have : ReflectsColimitsOfSize.{u,u} G := reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{u,u} (SheafOfModules.toSheaf B.ring) :=
    toSheaf_preservesColimits _
  have : (U.sheafRestrict (C := AddCommGrpCat.{u})).IsLeftAdjoint :=
    openAddSheafRestriction_isLeftAdjoint U
  have : PreservesColimitsOfSize.{u,u} (B.openRestriction U ⋙ G) :=
    preservesColimits_of_natIso (B.openRestrictionToSheafIso U).symm
  exact preservesColimits_of_reflects_of_preserves (B.openRestriction U) G

/--
概要：係数加群層の開制限は有限余極限を保つ。
方針：証明済みの小さい余極限保存を有限の場合へ制限する。
規約：有限極限の保存と合わせて完全性を与える。
使われ方：TT 3.19・8.1、Toën §3.2 の完全関手の導来化。
-/
instance openRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (B.openRestriction U) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

end CoefficientSheaf
end SerrePositivity.KST.DerivedGeometry
