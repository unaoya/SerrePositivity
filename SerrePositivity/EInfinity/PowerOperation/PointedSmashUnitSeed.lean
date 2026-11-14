module

public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlyingCoherence

/-!
# smash の右単位の逆を非基点側の射で読む

BF 1978 §2 の Γ スペクトルの構造射の照合に使う一般の補助。
既存の忘却の単位比較と右単位律だけから得る。［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.PointedSimplicialSet

lemma pointedSmashRightUnitor_inv (X : PointedSimplicialSet.{u}) :
    (ρ_ X).inv.right =
    (ρ_ X.right).inv ≫ (X.right ◁ forgetUnit) ≫
      productToSmash X (𝟙_ PointedSimplicialSet.{u}) := by
  have : IsIso (ρ_ X).hom.right :=
    (PointedSimplicialSet.forget).map_isIso (ρ_ X).hom
  apply (cancel_mono (ρ_ X).hom.right).mp
  rw [← Under.comp_right, Iso.inv_hom_id, Under.id_right]
  simp only [Category.assoc]
  rw [productToSmash_right_unitor, Iso.inv_hom_id]

end SerrePositivity.EInfinity.PowerOperation
