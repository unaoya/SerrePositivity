module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCornerMap
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCoconeIso
public import SerrePositivity.InfinityCategories.F2.Ind.ConeFoldNaturality

/-!
概要：一般の補間余錐と元の余錐の積の同型は、試験形状の射に厳密に自然。
方針：元の両座標の射影と、二重余錐の折り畳みの自然性を照合する。
規約：同じ元の順比較と逆比較を保持する。
使われ方：部分形状の全円柱を固定した点追加の再構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A B : SSet.{u}} (f : A ⟶ B) (L : SSet.{u})

/-- 概要：元の全補間余錐の比較は、試験形状の射と可換。
方針：二座標と折り畳みを照合。規約：全射の等号。使われ方：旧族の全円柱の回収。 -/
lemma coneTensorCocone_naturality :
    joinMap (coneTensorCornerMap f L) (𝟙 Δ[0]) ≫ coneTensorCocone B L =
      coneTensorCocone A L ≫ (joinMap f (𝟙 Δ[0]) ▷ join L (Δ[0] : SSet.{u})) := by
  have hx : coneTensorCornerMap f L ≫ coneTensorCornerInclusion B L ≫ fst _ _ =
      (coneTensorCornerInclusion A L ≫ fst _ _) ≫ joinMap f (𝟙 Δ[0]) := by
    rw [← Category.assoc, coneTensorCornerInclusion_naturality, Category.assoc,
      whiskerRight_fst, ← Category.assoc]
  have hy : coneTensorCornerMap f L ≫ coneTensorCornerInclusion B L ≫ snd _ _ =
      coneTensorCornerInclusion A L ≫ snd _ _ := by
    rw [← Category.assoc, coneTensorCornerInclusion_naturality, Category.assoc,
      whiskerRight_snd]
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, coneTensorCocone, lift_fst, lift_fst_assoc, whiskerRight_fst]
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, hx]
    rw [← arrowInterpolationConeFold_naturality, ← Category.assoc, ← joinMap_comp,
      Category.id_comp]
  · simp only [Category.assoc, coneTensorCocone, lift_snd, whiskerRight_snd]
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp, hy]

/-- 概要：元の全形状同型の逆も、試験形状の射と可換。
方針：順比較を合成して反映。規約：全射の等号。使われ方：旧族を固定した再構成。 -/
lemma coneTensorCoconeIso_inv_naturality :
    (joinMap f (𝟙 Δ[0]) ▷ join L (Δ[0] : SSet.{u})) ≫ (coneTensorCoconeIso B L).inv =
      (coneTensorCoconeIso A L).inv ≫ joinMap (coneTensorCornerMap f L) (𝟙 Δ[0]) := by
  apply (cancel_mono (coneTensorCoconeIso B L).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ = (coneTensorCoconeIso A L).inv ≫
    joinMap (coneTensorCornerMap f L) (𝟙 Δ[0]) ≫ coneTensorCocone B L
  rw [coneTensorCocone_naturality, ← Category.assoc]
  change _ = (coneTensorCoconeIso A L).inv ≫
    (coneTensorCoconeIso A L).hom ≫ (joinMap f (𝟙 Δ[0]) ▷ join L Δ[0])
  rw [Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2.Ind
