module

public import SerrePositivity.InfinityCategories.Stable.ExactFunctor
public import SerrePositivity.InfinityCategories.Stable.AdjunctionOpposite
public import SerrePositivity.InfinityCategories.F1B.QCatEquivalenceAdjunction
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalMappingContractible
public import SerrePositivity.InfinityCategories.HomotopyLimits.AdjunctionLimits
public import SerrePositivity.InfinityCategories.Core.TerminalTransport
public import SerrePositivity.InfinityCategories.Core.EquivalenceAllLimits

/-!
概要：安定 ∞ 圏の間の左随伴は零対象と cofiber 列を保つ。
方針：始対象性を随伴の写像空間比較で移し、押し出しを反対圏の引き戻しに移す。
使われ方：安定な層圏への反射の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

private def oppositeAdjunction {C E : SSet.{u}} [Quasicategory C] [Quasicategory E]
    {L : C ⟶ E} {R : E ⟶ C} (a : QCatAdjunction L R) :
    QCatAdjunction (opFunctor.map R) (opFunctor.map L) := by
  let c : C.op.op ≅ C := opFunctorCompOpFunctorIso.app C
  let e : E.op.op ≅ E := opFunctorCompOpFunctorIso.app E
  have b : QCatAdjunction ((c.hom ≫ L) ≫ e.inv) (e.hom ≫ R ≫ c.inv) :=
    ((qCatEquivalenceOfIso c).toAdjunction.comp a).comp
      (qCatEquivalenceOfIso e.symm).toAdjunction
  apply qcatAdjunctionOfOpposite
  have hL : opFunctor.map (opFunctor.map L) = (c.hom ≫ L) ≫ e.inv := by ext n x; rfl
  have hR : opFunctor.map (opFunctor.map R) = e.hom ≫ R ≫ c.inv := by ext n x; rfl
  rwa [hL, hR]

/-- 安定な値域で、左随伴による始対象と押し出しの保存は完全性を与える。 -/
lemma isExactFunctor_of_adjunction {C E : SSet.{u}} [Quasicategory C] [IsStable C]
    [Quasicategory E] [IsStable E] {L : C ⟶ E} {R : E ⟶ C}
    (a : QCatAdjunction L R) : IsExactFunctor L where
  preservesZero x hx := by
    have hi : IsInitialVertex (L.app _ x) := by
      apply isInitialVertex_of_intervalMappingSpace_isContractibleKan
      intro y
      exact (((unitMappingSpaceCondition_iff_interval a.unitHom).mp
        a.unitMappingSpaceCondition x y).isContractibleKan_iff).mpr
        (hx.1.intervalMappingSpace_isContractibleKan _)
    let z := chosenZeroVertex E
    exact ⟨hi, z.isTerminal.of_vertexIso (initialVertexIso z.isInitial hi)⟩
  preservesCofiber t ht := by
    change IsPushoutSquare (t.square ≫ L)
    rw [isPushoutSquare_iff_reverseGrid, reverseGrid_postcomp]
    let s := reverseGrid t.square
    have hs : IsPullbackSquare s := (isPushoutSquare_iff_reverseGrid t.square).mp ht
    have h := HomotopyLimits.mapJoinCone_isLimit_of_adjunction
      (oppositeAdjunction a) (pullbackCone s) hs
    exact (isLimitCone_iff_of_diagram_eq
      (Category.assoc _ _ _) (Category.assoc _ _ _)).mp h

end SerrePositivity.InfinityCategories
