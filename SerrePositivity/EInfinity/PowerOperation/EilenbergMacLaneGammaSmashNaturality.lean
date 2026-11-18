module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaSmash

/-!
# smash へ降ろした Γ の積の自然性

DAG XIII §2.2 の構造射に用いる。商からの引き戻しで指定された二項評価を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 同じ smart 切断・Γ・零基点による全関手。 -/
def gammaPointedFunctor : Complex A ⥤ PointedSimplicialSet.{u} :=
  (ComplexShape.embeddingUpIntLE 0).truncLE'Functor (ModuleCat A) ⋙
    (Abelian.DoldKan.Γ : ChainComplex (ModuleCat A) ℕ ⥤
      SimplicialObject (ModuleCat A)) ⋙ modulePointedFunctor A

lemma gammaPointedPair_naturality {K L K' L' : Complex A}
    (a : K ⟶ K') (b : L ⟶ L') :
    PointedObject.prodMap ((gammaPointedFunctor A).map a)
      ((gammaPointedFunctor A).map b) ≫ gammaPointedPair A K' L' =
    gammaPointedPair A K L ≫ (gammaPointedFunctor A).map (a ⊗ₘ b) := by
  apply Under.UnderMorphism.ext
  simp only [Under.comp_right, PointedObject.prodMap_right]
  change (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map a) ⊗ₘ
    ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map b)) ≫ gammaPair A K' L' =
      gammaPair A K L ≫ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (a ⊗ₘ b)
  exact gammaPair_naturality A a b

/-- 同じ smash 商を用いた二項評価は両変数で自然。 -/
lemma gammaSmashPair_naturality {K L K' L' : Complex A}
    (a : K ⟶ K') (b : L ⟶ L') :
    PointedObject.smashMap ((gammaPointedFunctor A).map a)
      ((gammaPointedFunctor A).map b) ≫ gammaSmashPair A K' L' =
    gammaSmashPair A K L ≫ (gammaPointedFunctor A).map (a ⊗ₘ b) := by
  apply PointedObject.smash_hom_ext
  rw [← Category.assoc, PointedObject.smashQuotient_map, Category.assoc]
  change PointedObject.prodMap ((gammaPointedFunctor A).map a)
    ((gammaPointedFunctor A).map b) ≫
      (PointedObject.smashQuotient (gammaPointed A K') (gammaPointed A L') ≫
        gammaSmashPair A K' L') =
    PointedObject.smashQuotient (gammaPointed A K) (gammaPointed A L) ≫
      gammaSmashPair A K L ≫ (gammaPointedFunctor A).map (a ⊗ₘ b)
  rw [gammaSmashPair_quotient, ← Category.assoc, gammaSmashPair_quotient]
  exact gammaPointedPair_naturality A a b

end SerrePositivity.EInfinity.PowerOperation
