module
public import SerrePositivity.KST.SConstruction.OneDirectionInverseMixedChoices
public import SerrePositivity.KST.SConstruction.PointedLiftTransportLaws

/-! # 逆射の混合切断空間の前後合成
概要：入力の合成を逆射の全パラメーター選択に作用させる。
方針：mapping path の厳密な関手性と持ち上げ空間の移送を使う。
規約：底の射と切断の条件を全次数で保持する。
使われ方：逆射の自然性ホモトピーの合成比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra Spectra.PointedMapping

/-- 入力の後合成を逆射の混合選択に作用させる。 -/
def oneDirectionInverseMixedPost (r : ℕ) {X Y Z : StableModel.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    oneDirectionInverseMixedChoices r f ⟶ oneDirectionInverseMixedChoices r (f ≫ g) :=
  pointedLiftTransport _ _ _ _ (𝟙 _) (oneDirectionMappingPathMap r g)
    ((boundaryKanRealizationFunctor r).map g) (oneDirectionMappingPathMap_projection r g)
    (by simp only [Category.id_comp, CategoryTheory.Functor.map_comp])

/-- 入力の前合成を逆射の混合選択に作用させる。 -/
def oneDirectionInverseMixedPre (r : ℕ) {X Y Z : StableModel.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    oneDirectionInverseMixedChoices r g ⟶ oneDirectionInverseMixedChoices r (f ≫ g) :=
  pointedLiftTransport _ _ _ _ ((boundaryKanRealizationFunctor r).map f) (𝟙 _) (𝟙 _)
    (by simp) (by simp only [Category.comp_id, CategoryTheory.Functor.map_comp])

/-- 源の逆射選択の後合成は合成入力の源の選択と一致する。 -/
lemma oneDirectionInverseMixedPost_source (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    oneDirectionInverseMixedFromSource r f ≫ oneDirectionInverseMixedPost r f g =
      oneDirectionInverseMixedFromSource r (f ≫ g) := by
  apply pullback.hom_ext
  · dsimp only [oneDirectionInverseMixedFromSource, oneDirectionInverseMixedPost]
    rw [Category.assoc, pointedLiftTransport_projection, ← Category.assoc,
      pointedLiftTransport_projection, Category.assoc, pointedMappingTransport_comp,
      pointedLiftTransport_projection, Category.id_comp, ← oneDirectionMappingPathMap_comp]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 標的の逆射選択の前合成は合成入力の標的の選択と一致する。 -/
lemma oneDirectionInverseMixedPre_target (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    oneDirectionInverseMixedFromTarget r g ≫ oneDirectionInverseMixedPre r f g =
      oneDirectionInverseMixedFromTarget r (f ≫ g) := by
  apply pullback.hom_ext
  · dsimp only [oneDirectionInverseMixedFromTarget, oneDirectionInverseMixedPre]
    rw [Category.assoc, pointedLiftTransport_projection, ← Category.assoc,
      pointedLiftTransport_projection, Category.assoc, pointedMappingTransport_comp,
      pointedLiftTransport_projection, Category.id_comp, ← CategoryTheory.Functor.map_comp]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

/-- 中間の逆射の選択を前後に移す二つの射は厳密に一致する。 -/
lemma oneDirectionInverseMixed_middle (r : ℕ) {X Y Z : StableModel.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    oneDirectionInverseMixedFromTarget r f ≫ oneDirectionInverseMixedPost r f g =
      oneDirectionInverseMixedFromSource r g ≫ oneDirectionInverseMixedPre r f g := by
  apply pullback.hom_ext
  · dsimp only [oneDirectionInverseMixedFromSource, oneDirectionInverseMixedFromTarget,
      oneDirectionInverseMixedPost, oneDirectionInverseMixedPre]
    simp only [Category.assoc, pointedLiftTransport_projection]
    rw [← Category.assoc, pointedLiftTransport_projection, Category.assoc,
      pointedMappingTransport_comp]
    rw [← Category.assoc, pointedLiftTransport_projection, Category.assoc,
      pointedMappingTransport_comp]
    simp only [Category.id_comp, Category.comp_id]
  · exact stdSimplex.isTerminalObj₀.hom_ext _ _

end SerrePositivity.KST.SConstruction
