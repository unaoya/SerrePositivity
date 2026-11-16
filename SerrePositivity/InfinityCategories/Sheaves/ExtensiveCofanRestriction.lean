module

public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveSieveCofinality
public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveSieveCone
public import SerrePositivity.InfinityCategories.Sheaves.ExtensiveIndexUniverseRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LeftCofinalUniverseLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.CofinalLimitTransfer
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.NerveConeCoherentComparison

/-!
概要：有限非空の余積被覆の指定制限錐を、元の脚の反対の指定積錐へ比較する。
方針：篩の全錐を共終な添字へ制限し、終点の値を指定右 Kan 条件で除いて全射を戻す。
  文献対応：HTT 6.2.2.6 の extensive 位相での層判定。
規約：初対象の値の終対象性を明示し、係数に極限の存在や保存性を仮定しない。
使われ方：S1 の有限積保存による層条件の判定。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {ι : Type u} {B : ι → C}
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 元の篩錐の有限添字への制限を同じ係数へ送る。 -/
abbrev cofanSieveCoefficientCone [HasInitial C] [Nonempty ι]
    (F : Presheaf C E) (c : Cofan B) :=
  ((nerveCone (cofanSieveIndexCone c)).ulift).postcomp F

/-- 元の篩錐を持ち上げた同じ添字へ制限すると、この全錐になる。 -/
lemma cofanSieveCoefficientCone_restrict_val [HasInitial C] [Nonempty ι]
    (F : Presheaf C E) (c : Cofan B) :
    (restrictJoinCone (restrictionCone F (cofanGeneratedSieve c))
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cofanSieveIndex c)))).val =
      (cofanSieveCoefficientCone F c).val := by
  change joinMap (𝟙 _) ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (cofanSieveIndex c))) ≫
    ((nerveCone (sieveCone (cofanGeneratedSieve c))).ulift.val ≫ F) = _
  rw [← Category.assoc, uliftNerveCone_whisker_val]
  rfl

/-- 脚の包含へ制限した全錐は、元の指定 fan の同じ係数による像。 -/
lemma cofanSieveCoefficientCone_legs_val [HasInitial C] [Nonempty ι]
    (F : Presheaf C E) (c : Cofan B) :
    (restrictJoinCone (cofanSieveCoefficientCone F c)
      ((SSet.uliftFunctor.{u + 1, u}).map
        (nerveMap (WithTerminal.incl : Discrete ι ⥤ WithTerminal (Discrete ι))))).val =
      (((nerveCone (cofanToOppositeFan c)).ulift).postcomp F).val := by
  change joinMap (𝟙 _) ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap WithTerminal.incl)) ≫
    ((nerveCone (cofanSieveIndexCone c)).ulift.val ≫ F) = _
  rw [← Category.assoc, uliftNerveCone_whisker_val]
  change ((uliftConeShapeIso (nerve (Discrete ι)) 0).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (nerveCone ((cofanSieveIndexCone c).whisker WithTerminal.incl)).val) ≫ F = _
  rw [cofanSieveIndexCone_legs_val]
  rfl

/-- 非空有限余積被覆の元の篩錐の極限性は、同じ元の脚の積錐の極限性と同値。 -/
lemma cofanRestriction_isLimit_iff [FinitaryExtensive C] [Finite ι] [Nonempty ι]
    (F : Presheaf C E)
    (h0 : IsTerminalVertex (F.app _ (ULift.up (nerveVertex (Opposite.op (⊥_ C))))))
    (c : Cofan B) (hc : IsColimit c) :
    IsLimitCone (restrictionCone F (cofanGeneratedSieve c)) ↔
      IsLimitCone (((nerveCone (cofanToOppositeFan c)).ulift).postcomp F) := by
  let H := (SSet.uliftFunctor.{u + 1, u}).map
    (nerveMap (cofanSieveIndex c ⋙ sieveDiagram (cofanGeneratedSieve c))) ≫ F
  have hstar : IsTerminalVertex
      (H.app _ (ULift.up (nerveVertex (WithTerminal.star : WithTerminal (Discrete ι))))) := by
    have hv : H.app (Opposite.op ⦋0⦌)
        (ULift.up (nerveVertex (WithTerminal.star : WithTerminal (Discrete ι)))) =
        F.app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex (Opposite.op (⊥_ C)))) := by
      change F.app (Opposite.op ⦋0⦌)
        (ULift.up ((ComposableArrows.mk₀ (WithTerminal.star : WithTerminal (Discrete ι))) ⋙
        (cofanSieveIndex c ⋙ sieveDiagram (cofanGeneratedSieve c)))) = _
      congr 1
    rw [hv]
    exact h0
  have hcofinal := isLeftCofinal_ulift.{u, u + 1} (nerveMap (cofanSieveIndex c))
    (cofanSieveIndex_isLeftCofinal c hc)
  exact (isLimitCone_iff_restrict_of_leftCofinal _ hcofinal _ _).trans
    ((isLimitCone_iff_of_cone_val_eq _ _ (cofanSieveCoefficientCone_restrict_val F c)).trans
      ((extensiveIndex_ulift_restrict_isLimit_iff (Discrete ι) H hstar
        (cofanSieveCoefficientCone F c)).trans
        (isLimitCone_iff_of_cone_val_eq _ _ (cofanSieveCoefficientCone_legs_val F c))))

end SerrePositivity.InfinityCategories.Sheaves
