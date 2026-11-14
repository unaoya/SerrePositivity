module
public import SerrePositivity.HomologicalAlgebra.CurriedDiagramHomotopy
/-!
概要：二重図式の指定鎖ホモトピーを積添字の同じ成分へ戻す。
方針：uncurryの射作用を次数ごとの自然変換へ適用する。
規約：IS-W2 A07の証明分割。ホモトピーの全成分を保持する。
使われ方：HA 1.2.4、指定区間による全余単体ホモトピー評価。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable {J K C : Type*} [Category* J] [Category* K] [Category* C] [Preadditive C]
variable {ι : Type*} (c : ComplexShape ι)
local notation "E₁" => functorToComplexOfFunctors (J × K) C c
local notation "E₂" =>
  (Functor.obj (Functor.whiskeringRight J (K ⥤ HomologicalComplex C c)
    (HomologicalComplex (K ⥤ C) c)) (functorToComplexOfFunctors K C c) ⋙
    functorToComplexOfFunctors J (K ⥤ C) c)
/-- 二重図式の同じホモトピーを積添字で評価する。 -/
def uncurriedDiagramHomotopy {F G : J ⥤ K ⥤ HomologicalComplex C c} (f g : F ⟶ G)
    (h : Homotopy ((E₂).map f) ((E₂).map g)) :
    Homotopy ((E₁).map (Functor.uncurry.map f)) ((E₁).map (Functor.uncurry.map g)) where
  hom i j := Functor.uncurry.map (h.hom i j)
  zero i j hij := by
    apply NatTrans.ext
    funext n
    exact NatTrans.congr_app (NatTrans.congr_app (h.zero i j hij) n.1) n.2
  comm i := by
    apply NatTrans.ext
    funext n
    exact NatTrans.congr_app (NatTrans.congr_app (h.comm i) n.1) n.2
end SerrePositivity.HomologicalAlgebra
