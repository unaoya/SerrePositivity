module
public import SerrePositivity.HomologicalAlgebra.NormalizedLinearWeightHom
/-!
概要：元の線形重みHom同値を全標的複体射に自然な形で使う。
方針：指定延長・切断・Dold–Kan同値の自然性と生成元評価を合成する。
規約：IS-W2 B02の前提計算2/3、既存構成の後合成則。全単体を保持する。
使われ方：HA 1.2.4、指定錐代表を移した実単体写像の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory HomologicalComplex AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {D : Type v} [Category.{w} D]
/-- 同じ元の線形重みHom同値は元の複体射による後合成と厳密に可換。 -/
theorem normalizedLinearWeightHomEquiv_postcomp (W : SimplicialObject (D ⥤ Type))
    {H H' : CochainComplex (D ⥤ ModuleCat A) ℤ}
    (f : ((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W)).extend
      ComplexShape.embeddingDownNat ⟶ H) (g : H ⟶ H') :
    normalizedLinearWeightHomEquiv A W H' (f ≫ g) =
      normalizedLinearWeightHomEquiv A W H f ≫
        Functor.whiskerRight
          ((Abelian.DoldKan.Γ : ChainComplex (D ⥤ ModuleCat A) ℕ ⥤
            SimplicialObject (D ⥤ ModuleCat A)).map
              (truncLE'Map g (ComplexShape.embeddingUpIntLE 0)))
          ((Functor.whiskeringRight D (ModuleCat A) (Type u)).obj (forget (ModuleCat A))) := by
  change copowerUnitBifunctorHomEquiv A W _
    (normalizedWeightHomEquiv (linearizedSimplicialWeight A W) H' (f ≫ g)) = _
  rw [normalizedWeightHomEquiv_postcomp]
  rfl
end SerrePositivity.HomologicalAlgebra
