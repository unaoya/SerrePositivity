module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanRealizationHom
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightFunctoriality

/-!
概要：BKパラメータ付き実現の指定随伴はsource frameの射について自然。
方針：既存の実現随伴の自然性を切断随伴との合成へ移す。
使われ方：HTT 4.2.4.4、RR02(a)の全source frameの比較。
規約：別の実現や非自然な成分ごとの逆射に置き換えない。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable (K : Type w) [SmallCategory K]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]

/-- 元の実現のsource射を、同じBKパラメータへ制限した自然変換。 -/
def bousfieldKanParameterMap {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B) :
    bousfieldKanParameterRealization K A ⟶ bousfieldKanParameterRealization K B :=
  Functor.whiskerLeft (weightedParameterFunctor (bousfieldKanWeight Kᵒᵖ)) (map K a)

/-- 合成随伴の転置は、source frameの射の全パラメータについて自然。 -/
lemma bousfieldKanParameterHomEquiv_frame_naturality
    {A B : K ⥤ SimplexCategory ⥤ C} (a : A ⟶ B) (T : SSet.{w}) (Y : C)
    (t : (bousfieldKanParameterRealization K B).obj T ⟶ Y) :
    (bousfieldKanParameterAdjunction K A).homEquiv T Y
        ((bousfieldKanParameterMap K a).app T ≫ t) =
      (bousfieldKanParameterAdjunction K B).homEquiv T Y t ≫
        weightedSectionsMap (bousfieldKanWeight Kᵒᵖ) (((homFamily K).map a.op).app Y) := by
  dsimp only [bousfieldKanParameterAdjunction, bousfieldKanParameterRealization,
    bousfieldKanParameterMap] at t ⊢
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  simp only [Equiv.trans_apply]
  change (weightedSectionsAdjunction (bousfieldKanWeight Kᵒᵖ)).homEquiv _ _
      ((adjunction K A).homEquiv _ Y ((map K a).app _ ≫ t)) = _
  rw [homEquiv_frame_naturality]
  exact (weightedSectionsAdjunction (bousfieldKanWeight Kᵒᵖ)).homEquiv_naturality_right
    ((adjunction K B).homEquiv _ Y t) (((homFamily K).map a.op).app Y)

end SerrePositivity.DiagramModel.FrameWeightRealization
