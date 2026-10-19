module
public import SerrePositivity.KST.SConstruction.ContractibleKanTriangles
public import SerrePositivity.KST.SConstruction.OneDirectionInverseMixedWhiskering

/-! # 比較逆射の自然性ホモトピーの合成三角形
概要：二本の入力と合成入力の指定した自然性の辺を一つの二単体へ補完する。
方針：端点の厳密な交換則で両辺を同じ混合選択空間へ移す。
規約：三本とも指定済みの辺を保持し、零次の選択を変更しない。
使われ方：スペクトルの構造射の coherent な自然性の二次段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open scoped Simplicial

/-- 前の入力の自然性の辺を合成入力の混合空間に移す。 -/
def oneDirectionInverseCompositionFirstEdge (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (v : (oneDirectionKanInverseChoices r X) _⦋0⦌)
    (w : (oneDirectionKanInverseChoices r Y) _⦋0⦌)
    (e : (oneDirectionInverseMixedChoices r f).Edge
      ((oneDirectionInverseMixedFromSource r f).app _ v)
      ((oneDirectionInverseMixedFromTarget r f).app _ w)) :
    (oneDirectionInverseMixedChoices r (f ≫ g)).Edge
      ((oneDirectionInverseMixedFromSource r (f ≫ g)).app _ v)
      ((oneDirectionInverseMixedPost r f g).app _ ((oneDirectionInverseMixedFromTarget r f).app _ w)) := by
  refine (e.map (oneDirectionInverseMixedPost r f g)).ofEq ?_ rfl
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (oneDirectionInverseMixedPost_source r f g) (Opposite.op ⦋0⦌)) v

/-- 後の入力の自然性の辺を同じ合成入力の混合空間に移す。 -/
def oneDirectionInverseCompositionSecondEdge (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : (oneDirectionKanInverseChoices r Y) _⦋0⦌)
    (v : (oneDirectionKanInverseChoices r Z) _⦋0⦌)
    (e : (oneDirectionInverseMixedChoices r g).Edge
      ((oneDirectionInverseMixedFromSource r g).app _ w)
      ((oneDirectionInverseMixedFromTarget r g).app _ v)) :
    (oneDirectionInverseMixedChoices r (f ≫ g)).Edge
      ((oneDirectionInverseMixedPost r f g).app _ ((oneDirectionInverseMixedFromTarget r f).app _ w))
      ((oneDirectionInverseMixedFromTarget r (f ≫ g)).app _ v) := by
  refine (e.map (oneDirectionInverseMixedPre r f g)).ofEq ?_ ?_
  · exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (oneDirectionInverseMixed_middle r f g).symm (Opposite.op ⦋0⦌)) w
  · exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (oneDirectionInverseMixedPre_target r f g) (Opposite.op ⦋0⦌)) v

/-- 指定した二本の自然性の辺と合成入力の辺を同時に回収する合成三角形。 -/
lemma oneDirectionInverseCompositionTriangle_nonempty (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (v₀ : (oneDirectionKanInverseChoices r X) _⦋0⦌)
    (v₁ : (oneDirectionKanInverseChoices r Y) _⦋0⦌)
    (v₂ : (oneDirectionKanInverseChoices r Z) _⦋0⦌)
    (e₀₁ : (oneDirectionInverseMixedChoices r f).Edge
      ((oneDirectionInverseMixedFromSource r f).app _ v₀)
      ((oneDirectionInverseMixedFromTarget r f).app _ v₁))
    (e₁₂ : (oneDirectionInverseMixedChoices r g).Edge
      ((oneDirectionInverseMixedFromSource r g).app _ v₁)
      ((oneDirectionInverseMixedFromTarget r g).app _ v₂))
    (e₀₂ : (oneDirectionInverseMixedChoices r (f ≫ g)).Edge
      ((oneDirectionInverseMixedFromSource r (f ≫ g)).app _ v₀)
      ((oneDirectionInverseMixedFromTarget r (f ≫ g)).app _ v₂)) :
    Nonempty (SSet.Edge.CompStruct (oneDirectionInverseCompositionFirstEdge r f g v₀ v₁ e₀₁)
      (oneDirectionInverseCompositionSecondEdge r f g v₁ v₂ e₁₂) e₀₂) :=
  contractibleKan_nonempty_compStruct (oneDirectionInverseMixedChoices_isContractibleKan r (f ≫ g)) _ _ _

end SerrePositivity.KST.SConstruction
