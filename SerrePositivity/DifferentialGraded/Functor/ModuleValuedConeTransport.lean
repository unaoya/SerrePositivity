module
public import SerrePositivity.DifferentialGraded.Functor.ModuleValuedCone
public import SerrePositivity.DifferentialGraded.Module.ConeTransportIso
/-!
概要：加群値 dg 関手の cone 比較を、指定した両端の実閉同型に沿って輸送する。
方針：元の cone 比較と arrow 圏からの厳密 cone 関手を合成する。
規約：両端同型と元の閉射を保持する。導来圏での同型に置き換えない。
使われ方：ラベル付き cone の評価比較を巨大な具体的延長式から切り離す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGFunctor
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (F : DGFunctor A (RightModule A D) (RightModule A E))
  {M N : ModuleCategory A D} (f : M ⟶ N)
  {M' N' : ModuleCategory A E} (a : F.onClosed.obj M ≅ M') (b : F.onClosed.obj N ≅ N')

def moduleValuedConeTransportIso :=
  (moduleValuedConeIso A D E F f).symm ≪≫
    moduleConeIsoOfSquare A E (F.onClosed.map f) (a.inv ≫ F.onClosed.map f ≫ b.hom)
      a b (by simp)

end SerrePositivity.DifferentialGraded.DGFunctor
