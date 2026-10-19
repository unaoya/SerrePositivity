module
public import SerrePositivity.InfinityCategories.Derived.CofiberSuspensionHomNormalization
public import SerrePositivity.InfinityCategories.Derived.FullInclusionHomotopyObjects
public import SerrePositivity.InfinityCategories.Derived.ChainMapEdge
public import SerrePositivity.InfinityCategories.Stable.ArrowFaithfulReflection
public import SerrePositivity.InfinityCategories.Stable.SquareEvaluationPostcomposition

/-! # Semifree 内の cofiber 比較の両端成分

概要：Semifree に持ち上げた比較は、始点で恒等射、終点で cone 写像の類を持つ。
方針：包含後の評価を反映し、全複体の成分計算と鎖写像の辺の式を使う。
規約：任意の semifree 間の鎖写像。使われ方：D7 の接続射の一意性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {S : Type u} [CommRing S] {X Y : Semifree S}

/-- Semifree の cofiber 比較の始点成分は恒等射。 -/
lemma semifreeCofiberSuspensionHom_source_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk ((squareDiagramHoEvaluation (derivedInfinityCategory S) 0 0).map
      (semifreeCofiberSuspensionHom f)) =
      Arrow.mk (𝟙 ((squareDiagramHoEvaluation (derivedInfinityCategory S) 0 0).obj
        (SSet.HomotopyCategory.mk (functorVertex (semifreeCofiberZeroTriangle f).square)))) := by
  let : (hoFunctor.map (derivedInfinityInclusion (S := S))).toFunctor.Faithful :=
    fullInclusionHo_faithful S (Complex S) (complexSemifree S)
  apply arrowMk_eq_of_faithful_map (hoFunctor.map derivedInfinityInclusion).toFunctor
    (fullInclusionHo_obj_injective S (Complex S) (complexSemifree S))
  calc
    _ = Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
        ((hoFunctor.map ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
          derivedInfinityInclusion)).toFunctor.map (semifreeCofiberSuspensionHom f))) :=
      (squareDiagramHoEvaluation_postcomp_arrow derivedInfinityInclusion
        (semifreeCofiberSuspensionHom f) 0 0).symm
    _ = Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).map
        (cofiberSuspensionHomOnInclusion f)) :=
      congrArg (squareDiagramHoEvaluation (dgNerve S (Complex S)) 0 0).mapArrow.obj
        (semifreeCofiberSuspensionHom_inclusion_arrow f)
    _ = _ := by
      rw [cofiberSuspensionHomOnInclusion_source_arrow, CategoryTheory.Functor.map_id]
      rfl

/-- Semifree の cofiber 比較の終点成分は cone 写像の類。 -/
lemma semifreeCofiberSuspensionHom_target_arrow (f : X.val ⟶ Y.val) :
    Arrow.mk ((squareDiagramHoEvaluation (derivedInfinityCategory S) 1 1).map
      (semifreeCofiberSuspensionHom f)) =
      Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (derivedChainMapEdge (x := Simplex.vertex (semifreeCofiberZeroObject f))
          (y := Simplex.vertex (semifreeSuspensionObject X)) (cofiberToSuspensionMap f))) := by
  let : (hoFunctor.map (derivedInfinityInclusion (S := S))).toFunctor.Faithful :=
    fullInclusionHo_faithful S (Complex S) (complexSemifree S)
  apply arrowMk_eq_of_faithful_map (hoFunctor.map derivedInfinityInclusion).toFunctor
    (fullInclusionHo_obj_injective S (Complex S) (complexSemifree S))
  calc
    _ = Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).map
        ((hoFunctor.map ((ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).map
          derivedInfinityInclusion)).toFunctor.map (semifreeCofiberSuspensionHom f))) :=
      (squareDiagramHoEvaluation_postcomp_arrow derivedInfinityInclusion
        (semifreeCofiberSuspensionHom f) 1 1).symm
    _ = Arrow.mk ((squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).map
        (cofiberSuspensionHomOnInclusion f)) :=
      congrArg (squareDiagramHoEvaluation (dgNerve S (Complex S)) 1 1).mapArrow.obj
        (semifreeCofiberSuspensionHom_inclusion_arrow f)
    _ = Arrow.mk (SSet.Truncated.HomotopyCategory.homMk
        (complexEdge (cofiberToSuspensionMap f)).toTruncated) :=
      cofiberSuspensionHomOnInclusion_target_arrow f
    _ = _ := by
      symm
      apply SSet.Truncated.HomotopyCategory.congr_arrowMk_homMk
      exact derivedChainMapEdge_inclusion (x := Simplex.vertex (semifreeCofiberZeroObject f))
        (y := Simplex.vertex (semifreeSuspensionObject X)) (cofiberToSuspensionMap f)

end SerrePositivity.InfinityCategories
