module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Coherent
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite

/-!
概要：元の全 Idem 図式の反転上の厳密な強い分裂を、元の分裂へ戻す。
方針：元の全包含の可換条件を反転し、二重反転の自然同型で元の図式へ戻す。
規約：対象だけでなく、指定した元の全図式の厳密な制限を保持する。
使われ方：極限から得た反転図式の余極限の強い分裂を元の図式へ戻す。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の全包含を反転した包含上で、元の反転図式を厳密に回収する強い分裂。 -/
def OppositeStrongSplitting {X : SSet.{u}} (d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X) :=
  {s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.op ⟶ X.op // SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion ≫ s = SSet.opFunctor.map d}

/-- 元の強い分裂を、同じ元の全図式とともに反転する。 -/
def StrongSplitting.toOpposite {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d) : OppositeStrongSplitting d :=
  ⟨SSet.opFunctor.map s.val, by
    rw [← SSet.opFunctor.map_comp, s.property]⟩

/-- 反転上の元の厳密な強い分裂から、元の全図式の厳密な強い分裂を回収する。 -/
def OppositeStrongSplitting.toStrong {X : SSet.{u}} {d : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CoherentIdempotent X}
    (s : OppositeStrongSplitting d) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.StrongSplitting d := by
  let eI := SSet.opFunctorCompOpFunctorIso.app _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape.{u}
  let eS := SSet.opFunctorCompOpFunctorIso.app _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.{u}
  let eX := SSet.opFunctorCompOpFunctorIso.app X
  refine ⟨eS.inv ≫ SSet.opFunctor.map s.val ≫ eX.hom, ?_⟩
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion ≫ eS.inv =
      eI.inv ≫ SSet.opFunctor.map (SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion) :=
    SSet.opFunctorCompOpFunctorIso.inv.naturality _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion
  have hd : SSet.opFunctor.map (SSet.opFunctor.map d) ≫ eX.hom = eI.hom ≫ d :=
    SSet.opFunctorCompOpFunctorIso.hom.naturality d
  have hs : SSet.opFunctor.map (SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion) ≫
      SSet.opFunctor.map s.val = SSet.opFunctor.map (SSet.opFunctor.map d) := by
    simpa only [Functor.map_comp] using congrArg SSet.opFunctor.map s.property
  calc
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion ≫ (eS.inv ≫ SSet.opFunctor.map s.val ≫ eX.hom) =
        eI.inv ≫ (SSet.opFunctor.map (SSet.opFunctor.map _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.idemInclusion) ≫
          SSet.opFunctor.map s.val) ≫ eX.hom := by
      rw [← Category.assoc, hi]
      simp only [Category.assoc]
    _ = eI.inv ≫ SSet.opFunctor.map (SSet.opFunctor.map d) ≫ eX.hom := by rw [hs]
    _ = d := by rw [hd, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
