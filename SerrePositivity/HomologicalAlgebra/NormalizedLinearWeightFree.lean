module
public import SerrePositivity.HomologicalAlgebra.CopowerUnitFree
public import SerrePositivity.HomologicalAlgebra.NormalizedLinearWeightHom

/-!
概要：元の指定余積による線形重みを、持ち上げた自由線形化と全図式で同定する。
方針：生成元を保つ自然同型を図式圏へ移し、Moore 正規化・負次数延長へ送る。
規約：単体方向も図式方向も省略せず、同じ正規化関手を使う。
使われ方：HA 1.2.4、G10 の指定 BK 重みと自由積比較の照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory HomologicalComplex AlgebraicTopology
namespace SerrePositivity.HomologicalAlgebra
variable (A : Type u) [CommRing A] {D : Type v} [Category.{w} D]

/-- 持ち上げた各単体の自由加群による重み。 -/
def freeLinearizedSimplicialWeight (W : SimplicialObject (D ⥤ Type)) :
    SimplicialObject (D ⥤ ModuleCat.{u} A) :=
  W ⋙ (Functor.whiskeringRight D (Type 0) (ModuleCat.{u} A)).obj
    (uliftFunctor.{u,0} ⋙ ModuleCat.free A)

/-- 指定余積から自由線形化への、両方向を保つ自然同型。 -/
def linearizedSimplicialWeightFreeIso (W : SimplicialObject (D ⥤ Type)) :
    linearizedSimplicialWeight A W ≅ freeLinearizedSimplicialWeight A W :=
  Functor.isoWhiskerLeft W
    ((Functor.whiskeringRight D (Type 0) (ModuleCat.{u} A)).mapIso (copowerUnitFreeNatIso A))

/-- 同じ比較は重みの全自然変換に自然。 -/
@[reassoc]
theorem linearizedSimplicialWeightFreeIso_naturality
    {W V : SimplicialObject (D ⥤ Type)} (f : W ⟶ V) :
    Functor.whiskerRight f ((Functor.whiskeringRight D (Type 0) (ModuleCat.{u} A)).obj
      (copowerFunctor (ModuleCat.of A A))) ≫ (linearizedSimplicialWeightFreeIso A V).hom =
    (linearizedSimplicialWeightFreeIso A W).hom ≫
      Functor.whiskerRight f ((Functor.whiskeringRight D (Type 0) (ModuleCat.{u} A)).obj
        (uliftFunctor.{u,0} ⋙ ModuleCat.free A)) := by
  apply NatTrans.ext
  funext n
  exact ((Functor.whiskeringRight D (Type 0) (ModuleCat.{u} A)).mapIso
    (copowerUnitFreeNatIso A)).hom.naturality (f.app n)

/-- 元の正規化線形重みと自由線形化の正規化との指定同型。 -/
def normalizedLinearWeightFreeIso (W : SimplicialObject (D ⥤ Type)) :
    (((normalizedMooreComplex _).obj (linearizedSimplicialWeight A W)).extend
      ComplexShape.embeddingDownNat) ≅
    (((normalizedMooreComplex _).obj (freeLinearizedSimplicialWeight A W)).extend
      ComplexShape.embeddingDownNat) :=
  (ComplexShape.embeddingDownNat.extendFunctor (D ⥤ ModuleCat.{u} A)).mapIso
    ((normalizedMooreComplex _).mapIso (linearizedSimplicialWeightFreeIso A W))

end SerrePositivity.HomologicalAlgebra
