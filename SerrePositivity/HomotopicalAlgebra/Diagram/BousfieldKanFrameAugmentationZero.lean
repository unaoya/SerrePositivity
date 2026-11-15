module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanFrameAugmentation
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameBousfieldKanAugmentation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexCosimplicialHom

/-!
概要：全余単体次数のBK実増大射の次数零は、指定した元の増大射と一致する。
方針：零単体とテンソル単位の同型を実現し、指定随伴の転置で照合する。
使われ方：HTT 4.2.4.4、RR02(a)の増大射の模型を保持する比較。
規約：増大射の弱同値性はこの照合から仮定しない。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.HomotopyFunctionComplex
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]

/-- 零単体パラメータを、元のBK重みへ移す既存の右単位同型。 -/
def bousfieldKanZeroParameterIso :
    (weightedParameterFunctor (bousfieldKanWeight Kᵒᵖ)).obj
        (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ≅ bousfieldKanWeight Kᵒᵖ :=
  tensorIso (Iso.refl _) ((Functor.const Kᵒᵖ).mapIso QuillenStandardFrame.zeroUnitIso) ≪≫
    ρ_ (bousfieldKanWeight Kᵒᵖ)

/-- 零単体への第二射影は同じ単位同型を介して元の重み射になる。 -/
lemma bousfieldKanZeroParameterIso_weight :
    (bousfieldKanZeroParameterIso K).hom ≫ bousfieldKanZeroWeight K =
      snd (bousfieldKanWeight Kᵒᵖ) (ConstantWeightHom.weight K (SimplexCategory.mk 0)) := by
  apply NatTrans.ext
  funext k
  exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

variable {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (A : K ⥤ SimplexCategory ⥤ C) (Q : SimplexCategory ⥤ C)
  (e : A ⟶ (Functor.const K).obj Q)

/-- 同じframe余錐の次数零。 -/
def bousfieldKanFrameZeroCocone : Cocone (ConstantWeightHom.degree K A (SimplexCategory.mk 0)) where
  pt := Q.obj (SimplexCategory.mk 0)
  ι := bousfieldKanCoconeDegree K A Q e (SimplexCategory.mk 0)

/-- 単位同型を実現した後、全frameの増大と元の次数零の増大は同じ実射になる。 -/
lemma bousfieldKanFrameAugmentation_zero :
    (functor K A).map (bousfieldKanZeroParameterIso K).hom ≫
        bousfieldKanAugmentation A (bousfieldKanFrameZeroCocone K A Q e) =
      (bousfieldKanFrameAugmentation K A Q e).app (SimplexCategory.mk 0) := by
  apply ((adjunction K A).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, bousfieldKanAugmentation_homEquiv]
  change (bousfieldKanZeroParameterIso K).hom ≫
      (bousfieldKanZeroWeight K ≫ bousfieldKanCoconeWeight K A Q e (SimplexCategory.mk 0)) =
    (adjunction K A).homEquiv _ _ (((adjunction K A).homEquiv _ _).symm
      (bousfieldKanCoconeParameter K A Q e (SimplexCategory.mk 0)))
  rw [Equiv.apply_symm_apply, ← Category.assoc, bousfieldKanZeroParameterIso_weight]
  rfl

end SerrePositivity.DiagramModel.FrameWeightRealization
