module
public import SerrePositivity.KST.SConstruction.PointedExtensionSpace
public import SerrePositivity.KST.Spectra.PostMappingLifts

/-! # 点つき持ち上げの可縮な選択空間
概要：全単射への RLP を持つ射に沿う持ち上げを全パラメーターで扱う。
方針：点つき写像空間の後合成の厳密な fiber を取る。
規約：源や標的の Kan 性を仮定しない。
使われ方：比較逆射の mapping path 切断の高次選択。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 指定した点つき射を厳密に持ち上げる射の空間。 -/
def pointedLiftSpace {A E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (b : A ⟶ B) : SSet.{u} :=
  pullback (PointedObject.basedHomMap A p).right (SSet.yonedaEquiv.symm (familyVertex b))

/-- 持ち上げ空間の一点への射影は trivial Kan fibration。 -/
lemma pointedLiftSpace_projection_trivialKanFibration {A E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right) (b : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.snd (PointedObject.basedHomMap A p).right
      (SSet.yonedaEquiv.symm (familyVertex b))) := by
  have hpost : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (PointedObject.basedHomMap A p).right :=
    ⟨post_rlp_monomorphisms A p hp⟩
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.pullback_snd _ _ hpost.mem⟩

/-- 持ち上げ空間は可縮 Kan であり、持ち上げの存在も含む。 -/
lemma pointedLiftSpace_isContractibleKan {A E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right) (b : A ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (pointedLiftSpace p b) := by
  have hp' := pointedLiftSpace_projection_trivialKanFibration p hp b
  intro n a
  have := hp'.mem (boundary n).ι inferInstance
  let sq : CommSq a (boundary n).ι
      (pullback.snd (PointedObject.basedHomMap A p).right
        (SSet.yonedaEquiv.symm (familyVertex b)))
      (stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u})) :=
    ⟨stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 持ち上げ空間のパラメーター族は任意の単射に沿って相対的に延長できる。 -/
lemma pointedLiftSpace_relative_lifting {A E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p.right) (b : A ⟶ B)
    {S T : SSet.{u}} (j : S ⟶ T) [Mono j] (a : S ⟶ pointedLiftSpace p b) :
    ∃ c : T ⟶ pointedLiftSpace p b, j ≫ c = a := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_iff_trivialKanFibration _).1
    (pointedLiftSpace_isContractibleKan p hp b)
  have := hc.mem j inferInstance
  let sq : CommSq a j (terminal.from (pointedLiftSpace p b)) (terminal.from T) :=
    ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 持ち上げ空間の頂点から実際の点つき射を回収する。 -/
def pointedLiftMap {A E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (b : A ⟶ B)
    (v : (pointedLiftSpace p b) _⦋0⦌) : A ⟶ E :=
  familyMap A E ((pullback.fst (PointedObject.basedHomMap A p).right
    (SSet.yonedaEquiv.symm (familyVertex b))).app (Opposite.op ⦋0⦌) v)

/-- 回収した射と元の射影の合成は指定した射を厳密に回収する。 -/
lemma pointedLiftMap_fac {A E B : PointedSimplicialSet.{u}} (p : E ⟶ B) (b : A ⟶ B)
    (v : (pointedLiftSpace p b) _⦋0⦌) : pointedLiftMap p b v ≫ p = b := by
  apply (familyVertexEquiv A B).injective
  change familyVertex (pointedLiftMap p b v ≫ p) = familyVertex b
  rw [← familyVertex_post]
  unfold pointedLiftMap
  rw [familyVertex_familyMap]
  have hc := ConcreteCategory.congr_hom (NatTrans.congr_app
    (pullback.condition (f := (PointedObject.basedHomMap A p).right)
      (g := SSet.yonedaEquiv.symm (familyVertex b))) (Opposite.op ⦋0⦌)) v
  have hv : (pullback.snd (PointedObject.basedHomMap A p).right
      (SSet.yonedaEquiv.symm (familyVertex b))).app (Opposite.op ⦋0⦌) v =
      SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
    apply stdSimplex.objEquiv.injective
    exact Subsingleton.elim _ _
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hc
  rw [hv, SSet.yonedaEquiv_symm_app_id] at hc
  exact hc

end SerrePositivity.KST.SConstruction
