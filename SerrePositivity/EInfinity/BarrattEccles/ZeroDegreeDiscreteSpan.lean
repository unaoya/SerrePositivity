module

public import SerrePositivity.EInfinity.BarrattEccles.ZeroDegreeHomologyIso

/-!
# 零次ホモロジーに集中する E 代数から離散代数への実擬同型の span

概要：元の包含と零次模型の標準 H⁰ 同型を使い、実代数射の擬同型二射を得る。
方針：切断商射を全 E 代数同型と合成する。
規約：元の代数に cofibrancy・厳密支持を仮定しない。
使われ方：CAlg_R における離散像の逆包含。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : (operad A).Algebra)

def zeroDegreeDiscreteAlgebra : CommAlgCat.{u} A :=
  homologyCommAlgebra (zeroDegreeModel A B)

def zeroDegreeDiscreteComparison :
    connectiveCover A B ⟶ (discreteAlgebraFunctor A).obj (zeroDegreeDiscreteAlgebra A B) := by
  let := zeroDegreeModel_nonpositive A B
  let := zeroDegreeModel_nonnegative A B
  exact zeroDegreeModelProjection A B ≫ (zeroDegreeHomologyAlgebraIso A (zeroDegreeModel A B)).hom

lemma zeroDegreeDiscreteComparison_quasiIso [B.carrier.IsLE 0] [B.carrier.IsGE 0] :
    QuasiIso (zeroDegreeDiscreteComparison A B).hom := by
  let := zeroDegreeModel_nonpositive A B
  let := zeroDegreeModel_nonnegative A B
  have := zeroDegreeModelProjection_quasiIso A B
  have : QuasiIso (zeroDegreeHomologyAlgebraIso A (zeroDegreeModel A B)).hom.hom := by
    change QuasiIso (_root_.SerrePositivity.HomologyZero.zeroDegreeHomologyIso (zeroDegreeModel A B).carrier).hom
    infer_instance
  change QuasiIso ((zeroDegreeModelProjection A B).hom ≫
    (zeroDegreeHomologyAlgebraIso A (zeroDegreeModel A B)).hom.hom)
  infer_instance

end SerrePositivity.EInfinity.BarrattEccles
