module
public import SerrePositivity.InfinityCategories.Core.UniverseJoinSimplexNaturality

/-! # 錐・余錐の全写像の宇宙移送

概要：標準単体付き join からの全写像は宇宙持ち上げの前後で全単射に対応する。
方針：形状の実同型と SSet の ULift の完全忠実性を組み合わせる。
規約：図式の固定条件は後続で制限する。使われ方：slice/coslice の各次数の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
open scoped Simplicial

/-- 錐の形状からの全写像の宇宙比較。 -/
def uliftConeHomEquiv (K X : SSet.{u}) (n : ℕ) :
    (join (Δ[n] : SSet.{u}) K ⟶ X) ≃
      (join (Δ[n] : SSet.{max u v}) ((SSet.uliftFunctor.{v, u}).obj K) ⟶
        (SSet.uliftFunctor.{v, u}).obj X) where
  toFun F := (uliftConeShapeIso.{u, v} K n).inv ≫ (SSet.uliftFunctor.{v, u}).map F
  invFun G := (SSet.uliftFunctor.{v, u}).preimage ((uliftConeShapeIso.{u, v} K n).hom ≫ G)
  left_inv F := by
    apply (SSet.uliftFunctor.{v, u}).map_injective
    rw [Functor.map_preimage, Iso.hom_inv_id_assoc]
  right_inv G := by
    change (uliftConeShapeIso.{u, v} K n).inv ≫ (SSet.uliftFunctor.{v, u}).map
      ((SSet.uliftFunctor.{v, u}).preimage ((uliftConeShapeIso.{u, v} K n).hom ≫ G)) = G
    rw [(SSet.uliftFunctor.{v, u}).map_preimage, Iso.inv_hom_id_assoc]

/-- 余錐の形状からの全写像の宇宙比較。 -/
def uliftCoconeHomEquiv (K X : SSet.{u}) (n : ℕ) :
    (join K (Δ[n] : SSet.{u}) ⟶ X) ≃
      (join ((SSet.uliftFunctor.{v, u}).obj K) (Δ[n] : SSet.{max u v}) ⟶
        (SSet.uliftFunctor.{v, u}).obj X) where
  toFun F := (uliftCoconeShapeIso.{u, v} K n).inv ≫ (SSet.uliftFunctor.{v, u}).map F
  invFun G := (SSet.uliftFunctor.{v, u}).preimage ((uliftCoconeShapeIso.{u, v} K n).hom ≫ G)
  left_inv F := by
    apply (SSet.uliftFunctor.{v, u}).map_injective
    rw [Functor.map_preimage, Iso.hom_inv_id_assoc]
  right_inv G := by
    change (uliftCoconeShapeIso.{u, v} K n).inv ≫ (SSet.uliftFunctor.{v, u}).map
      ((SSet.uliftFunctor.{v, u}).preimage ((uliftCoconeShapeIso.{u, v} K n).hom ≫ G)) = G
    rw [(SSet.uliftFunctor.{v, u}).map_preimage, Iso.inv_hom_id_assoc]

/-- 全錐写像の比較は可変単体の引き戻しと可換。 -/
lemma uliftConeHomEquiv_precomp (K X : SSet.{u}) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (F : join (Δ[n] : SSet.{u}) K ⟶ X) :
    uliftConeHomEquiv.{u, v} K X m (joinMap (stdSimplex.map α) (𝟙 K) ≫ F) =
      joinMap (stdSimplex.map α) (𝟙 ((SSet.uliftFunctor.{v, u}).obj K)) ≫
        uliftConeHomEquiv K X n F := by
  change (uliftConeShapeIso.{u, v} K m).inv ≫ (SSet.uliftFunctor.{v, u}).map (_ ≫ F) =
    joinMap (stdSimplex.map α) (𝟙 ((SSet.uliftFunctor.{v, u}).obj K)) ≫
      ((uliftConeShapeIso.{u, v} K n).inv ≫ (SSet.uliftFunctor.{v, u}).map F)
  rw [Functor.map_comp, ← Category.assoc, ← uliftConeShapeIso_inv_map, Category.assoc]

/-- 全余錐写像の比較は可変単体の引き戻しと可換。 -/
lemma uliftCoconeHomEquiv_precomp (K X : SSet.{u}) {m n : ℕ}
    (α : ⦋m⦌ ⟶ ⦋n⦌) (F : join K (Δ[n] : SSet.{u}) ⟶ X) :
    uliftCoconeHomEquiv.{u, v} K X m (joinMap (𝟙 K) (stdSimplex.map α) ≫ F) =
      joinMap (𝟙 ((SSet.uliftFunctor.{v, u}).obj K)) (stdSimplex.map α) ≫
        uliftCoconeHomEquiv K X n F := by
  change (uliftCoconeShapeIso.{u, v} K m).inv ≫ (SSet.uliftFunctor.{v, u}).map (_ ≫ F) =
    joinMap (𝟙 ((SSet.uliftFunctor.{v, u}).obj K)) (stdSimplex.map α) ≫
      ((uliftCoconeShapeIso.{u, v} K n).inv ≫ (SSet.uliftFunctor.{v, u}).map F)
  rw [Functor.map_comp, ← Category.assoc, ← uliftCoconeShapeIso_inv_map, Category.assoc]

end SerrePositivity.InfinityCategories
