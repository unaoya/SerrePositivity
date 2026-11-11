module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SquareVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：積上の可換四角形と四角形空間のパラメーター族の厳密な同型。
方針：内部 currying と右随伴による引き戻しの保存を使う。
規約：表現の fiber 条件は後段で比較する。
使われ方：点上の表現の区間族を実際の区間上の表現と結ぶ。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：内部 currying は係数への後合成と厳密に可換。
方針：二回 uncurry し評価と結合子の自然性を使う。
規約：任意の単体集合と射を扱う。
使われ方：四角形の pointed space 側の currying。 -/
lemma transportIhomCurry_naturality (A K : SSet.{u}) {X Y : SSet.{u}} (f : X ⟶ Y) :
    (ihom (A ⊗ K)).map f ≫ (ihomCurryIso A K Y).hom =
      (ihomCurryIso A K X).hom ≫ (ihom K).map ((ihom A).map f) := by
  change _ ≫ ihomCurry A K Y = ihomCurry A K X ≫ _
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_uncurry_ihomCurry]
  rw [uncurry_ihom_map]
  rw [associator_inv_naturality_right_assoc, ← uncurry_eq, uncurry_ihom_map]
  rw [uncurry_natural_right]
  simpa only [uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc] using
    congrArg (fun g ↦ g ≫ f) (uncurry_uncurry_ihomCurry A K X).symm

/-- 概要：積上の四角形全体は四角形空間へのパラメーター族と厳密に同型。
方針：内部 Hom の二射影を curry し、引き戻しの保存同型へ続ける。
規約：射影 p とパラメーター K の充填性は不要。
使われ方：区間や高次パラメーター上の表現空間の比較の周囲の同型。 -/
def transportSquareTensorIso {E B : SSet.{u + 1}} (p : E ⟶ B) (K : SSet.{u + 1}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace (p ▷ K) ≅ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace p) := by
  let f := (ihom E).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
  let g := (pre p).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity
  let fT := (ihom (E ⊗ K)).map _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
  let gT := (pre (p ▷ K)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity
  let eE := ihomCurryIso E K _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity
  let eB := ihomCurryIso B K _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity
  let eC := ihomCurryIso E K _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity
  have hE : fT ≫ eC.hom = eE.hom ≫ (ihom K).map f :=
    transportIhomCurry_naturality E K _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
  have hB : gT ≫ eC.hom = eB.hom ≫ (ihom K).map g :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ihomCurry_pre_whiskerRight p K _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace (p ▷ K)
  let P := pullback ((ihom K).map f) ((ihom K).map g)
  let t₀ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquarePointed (p ▷ K)
  let t₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareDiagram (p ▷ K)
  let p₀ : P ⟶ _ := pullback.fst _ _
  let p₁ : P ⟶ _ := pullback.snd _ _
  have hF : (t₀ ≫ eE.hom) ≫ (ihom K).map f = (t₁ ≫ eB.hom) ≫ (ihom K).map g := by
    simp only [Category.assoc]
    rw [← hE, ← hB, ← Category.assoc t₀ fT, ← Category.assoc t₁ gT]
    exact congrArg (fun h ↦ h ≫ eC.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportSquareSpace_condition (p ▷ K))
  let F : T ⟶ P := pullback.lift (t₀ ≫ eE.hom) (t₁ ≫ eB.hom) hF
  have hF₀ : F ≫ p₀ = t₀ ≫ eE.hom := pullback.lift_fst _ _ _
  have hF₁ : F ≫ p₁ = t₁ ≫ eB.hom := pullback.lift_snd _ _ _
  have hG : (p₀ ≫ eE.inv) ≫ fT = (p₁ ≫ eB.inv) ≫ gT := by
    apply (cancel_mono eC.hom).1
    simp only [Category.assoc]
    rw [hE, hB, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
    exact pullback.condition
  let G : P ⟶ T := pullback.lift (p₀ ≫ eE.inv) (p₁ ≫ eB.inv) hG
  have hG₀ : G ≫ t₀ = p₀ ≫ eE.inv := pullback.lift_fst _ _ _
  have hG₁ : G ≫ t₁ = p₁ ≫ eB.inv := pullback.lift_snd _ _ _
  let e : T ≅ P :=
    { hom := F, inv := G
      hom_inv_id := by
        apply pullback.hom_ext
        · change (F ≫ G) ≫ t₀ = (𝟙 T) ≫ t₀
          rw [Category.assoc, hG₀, ← Category.assoc, hF₀]
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
        · change (F ≫ G) ≫ t₁ = (𝟙 T) ≫ t₁
          rw [Category.assoc, hG₁, ← Category.assoc, hF₁]
          simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · change (G ≫ F) ≫ p₀ = (𝟙 P) ≫ p₀
          rw [Category.assoc, hF₀, ← Category.assoc, hG₀]
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
        · change (G ≫ F) ≫ p₁ = (𝟙 P) ≫ p₁
          rw [Category.assoc, hF₁, ← Category.assoc, hG₁]
          simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp] }
  exact e ≪≫ (PreservesPullback.iso (ihom K) f g).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
