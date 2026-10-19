module
public import SerrePositivity.KST.SConstruction.SInterchangeIso
public import SerrePositivity.KST.SConstruction.SCofiberStableIso

/-! # 完全関手としての二重 S の交換同型
概要：二重 S 構成の転置を安定な入力の圏での厳密な同型にする。
方針：元の同型の自明 Kan fibration 性により完全性を得る。
規約：底の比較は全 gapped 図式の実際の転置。使われ方：S₁ を有限反復の内外へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories

/-- 全 gapped 図式の二方向の転置は完全関手の圏での厳密な同型。 -/
def sInterchangeStableIso (m n : ℕ) (X : StableModel.{u}) :
    sStableModel m (sStableModel n X) ≅ sStableModel n (sStableModel m X) where
  hom := ⟨(sInterchangeIso m n X.carrier).hom, by
    have : IsIso (sInterchangeIso m n X.carrier).hom := inferInstance
    exact (preservesSConstructionData_of_trivialKanFibration _).toCofiberData⟩
  inv := ⟨(sInterchangeIso m n X.carrier).inv, by
    have : IsIso (sInterchangeIso m n X.carrier).inv := inferInstance
    exact (preservesSConstructionData_of_trivialKanFibration _).toCofiberData⟩
  hom_inv_id := Subtype.ext (sInterchangeIso m n X.carrier).hom_inv_id
  inv_hom_id := Subtype.ext (sInterchangeIso m n X.carrier).inv_hom_id

end SerrePositivity.KST.SConstruction
