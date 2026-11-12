module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphPerfectNativeAction
public import SerrePositivity.KST.SConstruction.PerfectDGExtension

/-!
概要：保存済み比較射の同じ実 Perf 延長を全 native 射として保持する。
方針：同じ厳密変換を実 Perf 延長・元包含で写し、二段後合成と照合する。
規約：元射を共役で再定義しない。使われ方：中央射の native 全比較の右辺。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (B E : Type (max (u + 1) v))
  [DGCategory R B] [Small.{u} B] [DGCategory R E] [Small.{u} E]
  (F G : DGFunctor R B B) (τ : DGFunctorParamTrans R B B (𝟙_ (Complex R)) F G)
local notation "P" => DGCategoryCellResolution.Source R B
local notation "Fp" => dgCellResolvedGraphPerfectFunctor R B F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B F)
local notation "Gp" => dgCellResolvedGraphPerfectFunctor R B G (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCellResolvedGraph_projective R B G)
local notation "η" => dgCellResolvedGraphPerfectStrictNatTrans R B F G τ
local notation "J" => perfectDGModuleInclusion R (P) Set.univ
local notation "I" => perfectDGModuleInclusion R E Set.univ

/-- 概要：元比較の同じ実 Perf 延長後の厳密 dg 変換。
方針：元の全厳密変換を実延長で後合成する。規約：元閉零成分を保持。
使われ方：同じ実商上の中央比較の Perf 表示。 -/
def dgCellResolvedGraphPerfectExtendedStrictNatTrans (projection : DGFunctor R (P) E) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (η) (perfectDGExtension R (P) E projection)

/-- 概要：同じ実 Perf 延長比較の元包含後の全 native 射。
方針：実二段後合成の厳密変換を同じ nerve で写す。
規約：元射を変更しない。使われ方：二成分全比較の自然性の実終端。 -/
def dgCellResolvedGraphPerfectExtendedNerveArrow (projection : DGFunctor R (P) E) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (((Fp).comp (perfectDGExtension R (P) E projection)).comp (I)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (((Gp).comp (perfectDGExtension R (P) E projection)).comp (I))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (P) (RightModule R E)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp (dgCellResolvedGraphPerfectExtendedStrictNatTrans R B E F G τ projection) (I))

/-- 概要：実二段延長の同じ全 native 射は共通 Perf 比較族の元射作用。
方針：厳密変換の二段後合成・元延長包含等号を保持する。
規約：全単体の射を照合。使われ方：native 全比較 square の実右辺。 -/
lemma dgCellResolvedGraphPerfectExtendedNerveArrow_family_heq (projection : DGFunctor R (P) E) :
    HEq (dgCellResolvedGraphPerfectExtendedNerveArrow R B E F G τ projection)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Fp)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Gp))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((J).comp (dgModuleExtension R (P) E projection)))
        (dgCellResolvedGraphPerfectNerveArrow R B F G τ)) := by
  let H := perfectDGExtension R (P) E projection
  let a := dgCellResolvedGraphPerfectNerveArrow R B F G τ
  let b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom R (P) (PerfectDGModule R E)
    (dgCellResolvedGraphPerfectExtendedStrictNatTrans R B E F G τ projection)
  have h₀ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_postcomp_heq R (P) (PerfectDGModule R E) (RightModule R E)
    (dgCellResolvedGraphPerfectExtendedStrictNatTrans R B E F G τ projection) (I)
  have h₁ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransNerveHom_postcomp_heq R (P) (PerfectDGModule R (P))
    (PerfectDGModule R E) (η) H
  have h₂ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_heq b _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (Fp) H) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp (Gp) H)
    h₁ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I))
  have h₃ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Fp)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (Gp))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I)) a
  have hk : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map H ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (I) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((J).comp (dgModuleExtension R (P) E projection)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp H (I)).symm.trans
      (congrArg (fun L => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map L) (perfectDGExtension_inclusion R (P) E projection))
  have h₄ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp_heq_of_target_eq a hk
  exact h₀.trans (h₂.trans ((heq_of_eq h₃).trans h₄))

end SerrePositivity.KST.SConstruction
