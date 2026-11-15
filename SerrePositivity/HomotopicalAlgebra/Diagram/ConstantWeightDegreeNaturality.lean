module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightHom

/-!
概要：定値標準単体重みのYoneda同値は余単体次数について自然。
方針：既存の単体的Yonedaの前合成自然性を成分ごとに適用する。
使われ方：HTT 4.2.4.4、RR02(a)の実増大射の全余単体次数での照合。
規約：frameの弱同値性はこの法則に不要。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.DiagramModel.ConstantWeightHom
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{w} C]
  (A : K ⥤ SimplexCategory ⥤ C)

/-- 既存の評価関手による、余単体次数の射の作用。 -/
def degreeTransition {n m : SimplexCategory} (f : n ⟶ m) :
    degree K A n ⟶ degree K A m :=
  Functor.whiskerLeft A ((evaluation SimplexCategory C).map f)

/-- 定値重みの制限は、余単体次数での前合成に対応する。 -/
lemma homEquiv_degree_naturality {n m : SimplexCategory} (f : n ⟶ m) (Y : C)
    (a : weight K m ⟶ (FrameWeightRealization.hom K A).obj Y) :
    homEquiv K A n Y ((Functor.const Kᵒᵖ).map (SSet.stdSimplex.map f) ≫ a) =
      degreeTransition K A f ≫ homEquiv K A m Y a := by
  apply NatTrans.ext
  funext k
  exact (SSet.yonedaEquiv_naturality f (a.app (Opposite.op k))).symm

end SerrePositivity.DiagramModel.ConstantWeightHom
