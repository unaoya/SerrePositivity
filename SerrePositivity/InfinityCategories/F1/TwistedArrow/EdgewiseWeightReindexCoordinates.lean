module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseWeightCoordinates
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseEndpoints

/-!
概要：edgewise 重みの添字変換を、同じ標準単体の左右の頂点で計算する。
方針：重みの同型を通して標準単体の射に移し、join の両包含で制限する。
規約：面・退化を含む任意の単体圏の射を扱う。
使われ方：混合 Hom の座標と実際の edgewise 重みの添字変換の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の重みの添字変換を標準単体の座標で表した実際の射。 -/
def edgewiseWeightStandardMap {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    (Δ[m + m + 1] : SSet.{u}) ⟶ Δ[n + n + 1] :=
  (edgewiseWeightIso m).inv ≫ edgewiseWeight.map α ≫ (edgewiseWeightIso n).hom

/-- 重みの実際の添字変換に対応する有限順序の射。 -/
def edgewiseWeightReindexOrderHom {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    Fin (m + m + 1 + 1) →o Fin (n + n + 1 + 1) :=
  (stdSimplex.objEquiv (SSet.yonedaEquiv (edgewiseWeightStandardMap.{u} α))).toOrderHom

/-- 順序射を標準単体へ写すと、元の重みから移した同じ射を回収する。 -/
lemma edgewiseWeightReindexOrderHom_map {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    stdSimplex.map (SimplexCategory.mkHom (edgewiseWeightReindexOrderHom.{u} α)) =
      edgewiseWeightStandardMap.{u} α := by
  exact SSet.yonedaEquiv.symm_apply_apply _

/-- 右半分への制限は元の添字変換の右区間への埋め込み。 -/
lemma edgewiseWeightStandardMap_right {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    stdSimplex.map (SimplexCategory.mkHom (DGNerve.joinRightOrderHom m m)) ≫
      edgewiseWeightStandardMap.{u} α =
    stdSimplex.map α ≫ stdSimplex.map
      (SimplexCategory.mkHom (DGNerve.joinRightOrderHom n n)) := by
  rw [← edgewiseWeightIso_inr, edgewiseWeightStandardMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change joinInr _ _ ≫ joinMap (SSet.opFunctor.map (stdSimplex.map α)) (stdSimplex.map α) ≫
    (edgewiseWeightIso n).hom = _
  rw [joinInr_joinMap_assoc, edgewiseWeightIso_inr]

/-- 左半分への制限は添字変換を反転した射の左区間への埋め込み。 -/
lemma edgewiseWeightStandardMap_left {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌) :
    stdSimplex.map (SimplexCategory.mkHom (DGNerve.joinLeftOrderHom m m)) ≫
      edgewiseWeightStandardMap.{u} α =
    stdSimplex.map (SimplexCategory.rev.map α) ≫ stdSimplex.map
      (SimplexCategory.mkHom (DGNerve.joinLeftOrderHom n n)) := by
  have hleft (k : ℕ) : stdSimplex.map
      (SimplexCategory.mkHom (DGNerve.joinLeftOrderHom k k)) =
      (stdSimplex.opIso ⦋k⦌).inv ≫ joinInl (Δ[k] : SSet.{u}).op Δ[k] ≫
        (edgewiseWeightIso k).hom := by
    rw [edgewiseWeightIso_inl, Iso.inv_hom_id_assoc]
  have hα := edgewiseStdSimplex_opIso_inv_naturality.{u} (SimplexCategory.rev.map α)
  rw [SimplexCategory.rev_map_rev_map] at hα
  change (stdSimplex.opIso ⦋m⦌).inv ≫ SSet.opFunctor.map (stdSimplex.map α) =
    stdSimplex.map (SimplexCategory.rev.map α) ≫ (stdSimplex.opIso ⦋n⦌).inv at hα
  rw [hleft m, edgewiseWeightStandardMap]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change (stdSimplex.opIso ⦋m⦌).inv ≫ joinInl _ _ ≫
    joinMap (SSet.opFunctor.map (stdSimplex.map α)) (stdSimplex.map α) ≫
      (edgewiseWeightIso n).hom = _
  rw [joinInl_joinMap_assoc, ← Category.assoc, hα, Category.assoc, hleft n]

/-- 重みの右頂点は元の添字写像で右頂点へ写る。 -/
lemma edgewiseWeightReindexOrderHom_right {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 1)) :
    edgewiseWeightReindexOrderHom.{u} α (edgewiseRightVertex m i) =
      edgewiseRightVertex n (α.toOrderHom i) := by
  have h := congrArg (fun f : (Δ[m] : SSet.{u}) ⟶ Δ[n + n + 1] =>
    (stdSimplex.objEquiv (SSet.yonedaEquiv f)).toOrderHom i)
    (edgewiseWeightStandardMap_right.{u} α)
  rw [← edgewiseWeightReindexOrderHom_map] at h
  exact h

/-- 重みの反転した左頂点も元の添字写像で対応する左頂点へ写る。 -/
lemma edgewiseWeightReindexOrderHom_left {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 1)) :
    edgewiseWeightReindexOrderHom.{u} α (edgewiseLeftVertex m i) =
      edgewiseLeftVertex n (α.toOrderHom i) := by
  have h := congrArg (fun f : (Δ[m] : SSet.{u}) ⟶ Δ[n + n + 1] =>
    (stdSimplex.objEquiv (SSet.yonedaEquiv f)).toOrderHom i.rev)
    (edgewiseWeightStandardMap_left.{u} α)
  rw [← edgewiseWeightReindexOrderHom_map] at h
  change edgewiseWeightReindexOrderHom.{u} α (DGNerve.joinLeftOrderHom m m i.rev) =
    DGNerve.joinLeftOrderHom n n ((SimplexCategory.rev.map α).toOrderHom i.rev) at h
  rw [SimplexCategory.rev_map_apply, Fin.rev_rev] at h
  have hv (k : ℕ) (j : Fin (k + 1)) :
      DGNerve.joinLeftOrderHom k k j.rev = edgewiseLeftVertex k j := by
    apply Fin.ext
    simp only [DGNerve.joinLeftOrderHom, OrderHom.coe_mk, Fin.val_rev,
      edgewiseLeftVertex]
    omega
  rw [hv, hv] at h
  exact h

end SerrePositivity.InfinityCategories
