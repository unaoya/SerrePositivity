module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanParameterizedRealization
public import SerrePositivity.HomotopicalAlgebra.Diagram.ConstantWeightDegreeNaturality

/-!
概要：指定frame余錐を、BK実現の全余単体次数の増大射へ移す。
方針：第二射影、定値重みのYoneda同値、元の実現随伴で転置する。
使われ方：HTT 4.2.4.4、RR02(a)の元のframeへの実比較射。
規約：増大射の弱同値性はここでは主張しない。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (A : K ⥤ SimplexCategory ⥤ C) (Q : SimplexCategory ⥤ C)
  (e : A ⟶ (Functor.const K).obj Q)

/-- 与えられたframe余錐を次数で評価した、そのままの脚。 -/
def bousfieldKanCoconeDegree (n : SimplexCategory) :
    ConstantWeightHom.degree K A n ⟶ (Functor.const K).obj (Q.obj n) :=
  Functor.whiskerRight e ((evaluation SimplexCategory C).obj n)

/-- 次数ごとの余錐の指定Yoneda転置。 -/
def bousfieldKanCoconeWeight (n : SimplexCategory) :
    ConstantWeightHom.weight K n ⟶ (hom K A).obj (Q.obj n) :=
  (ConstantWeightHom.homEquiv K A n (Q.obj n)).symm (bousfieldKanCoconeDegree K A Q e n)

/-- 指定Yoneda転置の次数自然性。 -/
lemma bousfieldKanCoconeWeight_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    (Functor.const Kᵒᵖ).map (SSet.stdSimplex.map f) ≫ bousfieldKanCoconeWeight K A Q e m =
      bousfieldKanCoconeWeight K A Q e n ≫ (hom K A).map (Q.map f) := by
  apply (ConstantWeightHom.homEquiv K A n (Q.obj m)).injective
  rw [ConstantWeightHom.homEquiv_degree_naturality,
    ConstantWeightHom.homEquiv_target_naturality]
  simp only [bousfieldKanCoconeWeight, Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext k
  exact (e.app k).naturality f

/-- BK重みを第二射影で忘れた、全次数の実現への入力。 -/
def bousfieldKanCoconeParameter (n : SimplexCategory) :
    (weightedParameterFunctor (bousfieldKanWeight Kᵒᵖ)).obj (SSet.stdSimplex.obj n) ⟶
      (hom K A).obj (Q.obj n) :=
  snd (bousfieldKanWeight Kᵒᵖ) (ConstantWeightHom.weight K n) ≫
    bousfieldKanCoconeWeight K A Q e n

/-- 第二射影とYoneda転置の次数自然性を合成する。 -/
lemma bousfieldKanCoconeParameter_naturality {n m : SimplexCategory} (f : n ⟶ m) :
    (weightedParameterFunctor (bousfieldKanWeight Kᵒᵖ)).map (SSet.stdSimplex.map f) ≫
        bousfieldKanCoconeParameter K A Q e m =
      bousfieldKanCoconeParameter K A Q e n ≫ (hom K A).map (Q.map f) := by
  dsimp only [bousfieldKanCoconeParameter]
  change (bousfieldKanWeight Kᵒᵖ ◁ (Functor.const Kᵒᵖ).map (SSet.stdSimplex.map f)) ≫
    snd _ _ ≫ _ = _
  rw [← Category.assoc, whiskerLeft_snd, Category.assoc,
    bousfieldKanCoconeWeight_naturality, ← Category.assoc]
  rfl

/-- 指定frame余錐から作る、全余単体次数の実増大射。 -/
def bousfieldKanFrameAugmentation :
    SSet.stdSimplex ⋙ bousfieldKanParameterRealization K A ⟶ Q where
  app n := ((adjunction K A).homEquiv _ _).symm (bousfieldKanCoconeParameter K A Q e n)
  naturality n m f := by
    apply ((adjunction K A).homEquiv _ _).injective
    change (adjunction K A).homEquiv _ _
      ((functor K A).map _ ≫ ((adjunction K A).homEquiv _ _).symm _) =
        (adjunction K A).homEquiv _ _
          (((adjunction K A).homEquiv _ _).symm _ ≫ Q.map f)
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
    simp only [Equiv.apply_symm_apply]
    exact bousfieldKanCoconeParameter_naturality K A Q e f

end SerrePositivity.DiagramModel.FrameWeightRealization
