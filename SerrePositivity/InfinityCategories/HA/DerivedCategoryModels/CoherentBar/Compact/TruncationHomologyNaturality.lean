module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MooreHomology
/-!
概要：既存の非正切断 Hom のホモロジー比較に、元の鎖写像の自然性を与える。
方針：延長のホモロジー同型と切断包含の自然性を合成する。
規約：切断・延長の同型の自然性は所有者の公開入口から受け取り、コピーしない。
使われ方：E2-S (8) の分離後に同じ比較へ代入する中間入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded HomologicalComplex
variable {R : Type u} [CommRing R] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [DGCategory R E]
  {x y : D} {a b : E}

lemma dgBarCompactConnectiveHomHomologyIso_naturality_of_truncation
    (φ : _root_.SerrePositivity.DifferentialGraded.homObject R D x y ⟶ _root_.SerrePositivity.DifferentialGraded.homObject R E a b)
    (ht : extendMap (truncLE'Map φ (ComplexShape.embeddingUpIntLE 0))
      (ComplexShape.embeddingUpIntLE 0) ≫
        ((_root_.SerrePositivity.DifferentialGraded.homObject R E a b).truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv =
      ((_root_.SerrePositivity.DifferentialGraded.homObject R D x y).truncLEIso (ComplexShape.embeddingUpIntLE 0)).inv ≫
        truncLEMap φ (ComplexShape.embeddingUpIntLE 0)) (n : ℕ) :
    homologyMap (truncLE'Map φ (ComplexShape.embeddingUpIntLE 0)) n ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.connectiveHomHomologyIso a b n).hom =
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.connectiveHomHomologyIso x y n).hom ≫ homologyMap φ (-(n : ℤ)) := by
  let e := ComplexShape.embeddingUpIntLE 0
  have he : e.f n = -(n : ℤ) := by simp [e]
  let K := _root_.SerrePositivity.DifferentialGraded.homObject R D x y
  let L := homObject R E a b
  let A := (K.truncLE' e).extendHomologyIso e he
  let B := (L.truncLE' e).extendHomologyIso e he
  have h₁ : homologyMap (truncLE'Map φ e) n ≫ B.inv =
      A.inv ≫ homologyMap (extendMap (truncLE'Map φ e) e) (-(n : ℤ)) := by
    apply (cancel_epi A.hom).mp
    rw [← Category.assoc, ← extendHomologyIso_hom_naturality _ _ he]
    simp only [A, B, K, L, Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id]
  have h₂ : homologyMap (extendMap (truncLE'Map φ e) e) (-(n : ℤ)) ≫
      homologyMap (L.truncLEIso e).inv (-(n : ℤ)) =
    homologyMap (K.truncLEIso e).inv (-(n : ℤ)) ≫
      homologyMap (truncLEMap φ e) (-(n : ℤ)) := by
    simpa only [homologyMap_comp] using
      congrArg (fun f => homologyMap f (-(n : ℤ))) ht
  have h₃ : homologyMap (truncLEMap φ e) (-(n : ℤ)) ≫
      homologyMap (HomologicalComplex.ιTruncLE L e) (-(n : ℤ)) =
    homologyMap (HomologicalComplex.ιTruncLE K e) (-(n : ℤ)) ≫ homologyMap φ (-(n : ℤ)) := by
    simpa only [homologyMap_comp] using
      congrArg (fun f => homologyMap f (-(n : ℤ))) (ιTruncLE_naturality φ e)
  change homologyMap (truncLE'Map φ e) n ≫
    (B.inv ≫ homologyMap (L.truncLEIso e).inv (-(n : ℤ)) ≫
      homologyMap (HomologicalComplex.ιTruncLE L e) (-(n : ℤ))) =
    (A.inv ≫ homologyMap (K.truncLEIso e).inv (-(n : ℤ)) ≫
      homologyMap (HomologicalComplex.ιTruncLE K e) (-(n : ℤ))) ≫ homologyMap φ (-(n : ℤ))
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]
  rw [← Category.assoc _ _ (homologyMap (HomologicalComplex.ιTruncLE L e) (-(n : ℤ))), h₂]
  simp only [Category.assoc]
  rw [h₃]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
