module
public import SerrePositivity.KST.SConstruction.ContractibleKanTriangles

/-! # Kan 随伴射の自然性ホモトピーの合成三角形
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
def kanAssemblyCompositionFirstEdge (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌)
    (e : (kanAssemblyMixedChoices r f).Edge
      ((kanAssemblyMixedFromSource r f).app _ v)
      ((kanAssemblyMixedFromTarget r f).app _ w)) :
    (kanAssemblyMixedChoices r (f ≫ g)).Edge
      ((kanAssemblyMixedFromSource r (f ≫ g)).app _ v)
      ((kanAssemblyMixedPost r f g).app _ ((kanAssemblyMixedFromTarget r f).app _ w)) := by
  refine (e.map (kanAssemblyMixedPost r f g)).ofEq ?_ rfl
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (kanAssemblyMixedPost_source r f g) (Opposite.op ⦋0⦌)) v

/-- 後の入力の自然性の辺を同じ合成入力の混合空間に移す。 -/
def kanAssemblyCompositionSecondEdge (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌)
    (v : (kanAssemblyAdjointChoices r Z) _⦋0⦌)
    (e : (kanAssemblyMixedChoices r g).Edge
      ((kanAssemblyMixedFromSource r g).app _ w)
      ((kanAssemblyMixedFromTarget r g).app _ v)) :
    (kanAssemblyMixedChoices r (f ≫ g)).Edge
      ((kanAssemblyMixedPost r f g).app _ ((kanAssemblyMixedFromTarget r f).app _ w))
      ((kanAssemblyMixedFromTarget r (f ≫ g)).app _ v) := by
  refine (e.map (kanAssemblyMixedPre r f g)).ofEq ?_ ?_
  · exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (kanAssemblyMixed_middle r f g).symm (Opposite.op ⦋0⦌)) w
  · exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (kanAssemblyMixedPre_target r f g) (Opposite.op ⦋0⦌)) v

/-- 指定した二本の自然性の辺と合成入力の辺を同時に回収する合成三角形。 -/
lemma kanAssemblyCompositionTriangle_nonempty (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (v₀ : (kanAssemblyAdjointChoices r X) _⦋0⦌)
    (v₁ : (kanAssemblyAdjointChoices r Y) _⦋0⦌)
    (v₂ : (kanAssemblyAdjointChoices r Z) _⦋0⦌)
    (e₀₁ : (kanAssemblyMixedChoices r f).Edge
      ((kanAssemblyMixedFromSource r f).app _ v₀)
      ((kanAssemblyMixedFromTarget r f).app _ v₁))
    (e₁₂ : (kanAssemblyMixedChoices r g).Edge
      ((kanAssemblyMixedFromSource r g).app _ v₁)
      ((kanAssemblyMixedFromTarget r g).app _ v₂))
    (e₀₂ : (kanAssemblyMixedChoices r (f ≫ g)).Edge
      ((kanAssemblyMixedFromSource r (f ≫ g)).app _ v₀)
      ((kanAssemblyMixedFromTarget r (f ≫ g)).app _ v₂)) :
    Nonempty (SSet.Edge.CompStruct (kanAssemblyCompositionFirstEdge r f g v₀ v₁ e₀₁)
      (kanAssemblyCompositionSecondEdge r f g v₁ v₂ e₁₂) e₀₂) :=
  contractibleKan_nonempty_compStruct (kanAssemblyMixedChoices_isContractibleKan r (f ≫ g)) _ _ _

end SerrePositivity.KST.SConstruction
