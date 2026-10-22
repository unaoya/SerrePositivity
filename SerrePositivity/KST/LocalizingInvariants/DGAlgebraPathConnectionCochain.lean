module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathCochainExt

/-!
概要：経路代数を二重経路へ送る connection の次数 -1 の比較成分。
方針：source を零、target を元の primitive、二重 primitive を零として指定する。
規約：四辺の経路を保持する。使われ方：動く境界の class 正方形の輪郭比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CochainComplex HomComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R] (B : Mon (Complex R))

/-- connection の全複体上の比較 cochain。 -/
def connectionCochain : Cochain (algebra R B).X (algebra R B).X (-1) :=
  mappingCocone.liftCochain (difference R B)
    ((primitive R B).comp
      (Cochain.ofHom (biprod.inr : B.X ⟶ B.X ⊞ B.X)) (add_zero (-1)))
    (0 : Cochain (algebra R B).X B.X (-2)) (by omega)

lemma connectionCochain_source :
    (connectionCochain R B).comp (Cochain.ofHom (source R B).hom) (add_zero (-1)) = 0 := by
  change (connectionCochain R B).comp
    (Cochain.ofHom (mappingCocone.fst (difference R B) ≫ biprod.fst)) _ = 0
  rw [Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain]
  change ((mappingCocone.liftCochain _ _ _ _).comp
    (Cochain.ofHom (mappingCocone.fst (difference R B))) _).comp _ _ = 0
  rw [mappingCocone.liftCochain_comp_fst, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, biprod.inr_fst, Cochain.ofHom_zero, Cochain.comp_zero]

lemma connectionCochain_target :
    (connectionCochain R B).comp (Cochain.ofHom (target R B).hom) (add_zero (-1)) =
      primitive R B := by
  change (connectionCochain R B).comp
    (Cochain.ofHom (mappingCocone.fst (difference R B) ≫ biprod.snd)) _ = _
  rw [Cochain.ofHom_comp, ← Cochain.comp_assoc_of_third_is_zero_cochain]
  change ((mappingCocone.liftCochain _ _ _ _).comp
    (Cochain.ofHom (mappingCocone.fst (difference R B))) _).comp _ _ = _
  rw [mappingCocone.liftCochain_comp_fst, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, biprod.inr_snd, Cochain.comp_id]

lemma connectionCochain_primitive :
    (connectionCochain R B).comp (primitive R B) (by omega : -1 + -1 = -2) = 0 := by
  exact mappingCocone.liftCochain_comp_snd _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
