module
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import SerrePositivity.HomologicalAlgebra.NormalizedWeightHom
public import SerrePositivity.HomologicalAlgebra.CopowerUnitHomBifunctor

/-!
概要：集合的な単体重みの実正規化鎖からの射を、Dold–Kan の集合値単体図式への射と同定する。
方針：図式圏での延長・切断・Dold–Kan Hom 同値に、二変数の生成元評価を合成する。
規約：単体方向と添字方向の全作用素を持つ自然変換。零次数の元だけへの置き換えではない。
使われ方：HA 1.2.4、G10 の正規化 BK 重みと切断空間の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits HomologicalComplex CochainComplex AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {D : Type v} [Category.{w} D]

/-- 各単体の指定単位余積による、集合的な単体重みの線形化。 -/
def linearizedSimplicialWeight (W : SimplicialObject (D ⥤ Type)) :
    SimplicialObject (D ⥤ ModuleCat.{u} A) :=
  W ⋙ (Functor.whiskeringRight D (Type 0) (ModuleCat.{u} A)).obj
    (copowerFunctor (ModuleCat.of A A))

/-- 実正規化した線形重みの Hom と、元の集合的重みからの単体的自然変換の同値。 -/
def normalizedLinearWeightHomEquiv (W : SimplicialObject (D ⥤ Type))
    (H : CochainComplex (D ⥤ ModuleCat.{u} A) ℤ) :
    (((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W)).extend
      ComplexShape.embeddingDownNat ⟶ H) ≃
    (W ⋙ (Functor.whiskeringRight D (Type 0) (Type u)).obj uliftFunctor.{u,0} ⟶
      ((Abelian.DoldKan.Γ : ChainComplex (D ⥤ ModuleCat.{u} A) ℕ ⥤
        SimplicialObject (D ⥤ ModuleCat.{u} A)).obj
          (H.truncLE' (ComplexShape.embeddingUpIntLE 0))) ⋙
        (Functor.whiskeringRight D (ModuleCat.{u} A) (Type u)).obj (forget (ModuleCat.{u} A))) :=
  (normalizedWeightHomEquiv (linearizedSimplicialWeight A W) H).trans
    (copowerUnitBifunctorHomEquiv A W _)

end SerrePositivity.HomologicalAlgebra
