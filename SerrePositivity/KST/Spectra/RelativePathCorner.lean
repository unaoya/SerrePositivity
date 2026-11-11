module

public import SerrePositivity.KST.Spectra.MappingCorner
public import SerrePositivity.KST.Spectra.MappingFiber

/-!
概要：射影された path と全空間の終点を同時に指定する相対 path fibration。
方針：点つき区間の終点包含の corner の標的を単位 Hom の同型で移す。
規約：path は基点に始まる。底の path と全空間の終点を同時に保つ。
使われ方：Goerss–Jardine I §8。二方向の連結射の共通持ち上げ。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.RelativePath

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E B : PointedSimplicialSet.{u}} (p : E ⟶ B)

/-- 単位からの Hom の標的評価は後合成と可換。 -/
@[reassoc]
lemma unitHom_map :
    (PointedObject.basedHomMap (𝟙_ PointedSimplicialSet.{u}) p).right ≫
        (MonoidalClosed.unitIsoSelf (X := B)).hom.right =
      (MonoidalClosed.unitIsoSelf (X := E)).hom.right ≫ p.right := by
  have h := (MonoidalClosed.unitNatIso (C := PointedSimplicialSet.{u})).inv.naturality p
  exact congrArg Under.Hom.right h

/-- 概要：区間の corner の標的を、底の path と全空間の終点の pullback へ同定する。
方針：単位 Hom の同型を pullback の第二射影に適用する。
規約：第一射影は底の path のまま。
使われ方：Goerss–Jardine I §8。path の具体的な相対持ち上げ先。 -/
def targetIso : PointedMapping.cornerTarget _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u} p ≅
    pullback (pathEndpoint B).right p.right where
  hom := pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (MonoidalClosed.unitIsoSelf (X := E)).hom.right) (by
      change pullback.fst _ _ ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint B ≫
          (MonoidalClosed.unitIsoSelf (X := B)).hom.right) = _
      simp only [Category.assoc]
      rw [← unitHom_map, ← pullback.condition_assoc])
  inv := pullback.lift (pullback.fst _ _)
    (pullback.snd _ _ ≫ (MonoidalClosed.unitIsoSelf (X := E)).inv.right) (by
      apply (cancel_mono (MonoidalClosed.unitIsoSelf (X := B)).hom.right).mp
      simp only [Category.assoc, unitHom_map]
      have heq : (MonoidalClosed.unitIsoSelf (X := E)).inv.right ≫
          (MonoidalClosed.unitIsoSelf (X := E)).hom.right ≫ p.right = p.right := by
        rw [← Category.assoc, show (MonoidalClosed.unitIsoSelf (X := E)).inv.right ≫
          (MonoidalClosed.unitIsoSelf (X := E)).hom.right = 𝟙 _ from
          congrArg Under.Hom.right (MonoidalClosed.unitIsoSelf (X := E)).inv_hom_id,
          Category.id_comp]
      erw [heq]
      exact pullback.condition)
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.id_comp]
    erw [Category.assoc, show (MonoidalClosed.unitIsoSelf (X := E)).hom.right ≫
      (MonoidalClosed.unitIsoSelf (X := E)).inv.right = 𝟙 _ from
      congrArg Under.Hom.right (MonoidalClosed.unitIsoSelf (X := E)).hom_inv_id]
    exact Category.comp_id _
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.id_comp]
    erw [Category.assoc, show (MonoidalClosed.unitIsoSelf (X := E)).inv.right ≫
      (MonoidalClosed.unitIsoSelf (X := E)).hom.right = 𝟙 _ from
      congrArg Under.Hom.right (MonoidalClosed.unitIsoSelf (X := E)).inv_hom_id]
    exact Category.comp_id _

/-- 概要：path を、底への射影と全空間での終点の組へ送る。
方針：区間の corner を具体的な pullback の同型へ合成する。
規約：通常の単体集合の射。
使われ方：Goerss–Jardine I §8。path と fiber の同時充填。 -/
def corner : (basedPathSpace E).right ⟶ pullback (pathEndpoint B).right p.right :=
  PointedMapping.corner _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.intervalEndpoint.{u} p ≫ (targetIso p).hom

@[reassoc (attr := simp)]
lemma corner_fst : corner p ≫ pullback.fst _ _ = (basedPathMap p).right := by
  simp only [corner, targetIso, Category.assoc, pullback.lift_fst,
    PointedMapping.corner_fst]
  rfl

@[reassoc (attr := simp)]
lemma corner_snd : corner p ≫ pullback.snd _ _ = (pathEndpoint E).right := by
  simp only [corner, targetIso, Category.assoc, pullback.lift_snd,
    PointedMapping.corner_snd_assoc]
  rfl

/-- 概要：底の path と全空間の終点の同時指定は Kan fibration。
方針：区間の終点包含の単射性と一般の corner fibration を使う。
規約：p の Kan fibration 性だけで、全空間・底の Kan 性は不要。
使われ方：Goerss–Jardine I §8。二つの連結射の共通持ち上げ。 -/
instance corner_fibration [Fibration p.right] : Fibration (corner p) := by
  dsimp only [corner]
  infer_instance

end
end SerrePositivity.KST.Spectra.RelativePath
