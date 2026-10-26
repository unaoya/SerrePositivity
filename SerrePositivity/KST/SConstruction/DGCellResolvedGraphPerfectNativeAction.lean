module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphPerfectNerveArrow
public import SerrePositivity.InfinityCategories.Derived.DGModuleDerivedFunctor
public import SerrePositivity.InfinityCategories.Derived.FunctorHomWhiskerMapTransport

/-!
概要：同じ Perf 比較射の native 導来延長作用を元 graph 比較の作用と全体で照合する。
方針：元包含射の型付き同定を実導来延長で後合成し、元関手圏の射を回収する。
規約：元 graph 比較と指定 dg 射を保持。使われ方：共通 Perf 比較族と native square の接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (B E : Type (max (u + 1) v))
  [DGCategory R B] [Small.{u} B] [DGCategory R E] [Small.{u} E]
local notation "P" => DGCategoryCellResolution.Source R B
local notation "J" => perfectDGModuleInclusion R (P) Set.univ
local notation "ρ" => dgModuleResolvedInfinity R (RightModule R (P)) (P)
  (DGFunctor.id (RightModule R (P)))
local notation "I" => dgFullSubcategoryInclusion R (RightModule R E) (dgModuleSemifreeProperty R E)

/-- 概要：元 graph 全関手射を同じ実導来延長と生包含で後合成する。
方針：同じ元関手圏の実作用を合成する。規約：元の指定 dg 射を保持。
使われ方：同じ Perf 比較射の native 作用の正本。 -/
def dgCellGraphExtendedNativeFunctor (projection : DGFunctor R (P) E) :
    BimoduleCategory R (P) (P) ⥤
      hoFunctor.obj ((ihom (dgNerve R (P))).obj (dgNerve R (RightModule R E))) :=
  dgCellGraphNativeFunctor R B ⋙ SSet.mapHomotopyCategory
    ((ihom (dgNerve R (P))).map
      (dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I)))

/-- 概要：共通 Perf 比較族での元射の作用は元 graph の同じ実 native 作用。
方針：包含同定と二段後合成の交換を貼る。規約：全関手射の値を保持。
使われ方：二成分比較と native square を同じ中央射で接続する。 -/
lemma dgCellResolvedGraphPerfectNativeAction_heq (F G : DGFunctor R B B)
    (τ : DGFunctorParamTrans R B B (𝟙_ (Complex R)) F G)
    (projection : DGFunctor R (P) E) :
    HEq (functorHomPostcomp
      (dgNerve.map (dgCellResolvedGraphPerfectFunctor R B F (dgCellResolvedGraph_projective R B F)))
      (dgNerve.map (dgCellResolvedGraphPerfectFunctor R B G (dgCellResolvedGraph_projective R B G)))
      ((dgNerve.map (J) ≫ (ρ)) ≫ dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I))
      (dgCellResolvedGraphPerfectNerveArrow R B F G τ))
      ((dgCellGraphExtendedNativeFunctor R B E projection).map (dgCellResolvedGraphMap R B F G τ)) := by
  let f := dgNerve.map (dgCellResolvedGraphPerfectFunctor R B F (dgCellResolvedGraph_projective R B F))
  let g := dgNerve.map (dgCellResolvedGraphPerfectFunctor R B G (dgCellResolvedGraph_projective R B G))
  let a := dgCellResolvedGraphPerfectNerveArrow R B F G τ
  let m := (dgBimoduleFunctorHomFunctor R (P) (P)).map (dgCellResolvedGraphMap R B F G τ)
  let K := dgModuleExtensionInfinity R (P) E projection ≫ dgNerve.map (I)
  have hF : f ≫ dgNerve.map (J) = dgNerve.map (dgCellResolvedGraphModuleFunctor R B F) :=
    (dgNerve.map_comp _ _).symm.trans (congrArg (fun L => dgNerve.map L)
      (dgCellResolvedGraphPerfectFunctor_inclusion R B F (dgCellResolvedGraph_projective R B F)))
  have hG : g ≫ dgNerve.map (J) = dgNerve.map (dgCellResolvedGraphModuleFunctor R B G) :=
    (dgNerve.map_comp _ _).symm.trans (congrArg (fun L => dgNerve.map L)
      (dgCellResolvedGraphPerfectFunctor_inclusion R B G (dgCellResolvedGraph_projective R B G)))
  have h₀ := functorHomPostcomp_heq_of_target_eq a (Category.assoc (dgNerve.map (J)) (ρ) K)
  have h₁ := functorHomPostcomp_postcomp f g (dgNerve.map (J)) ((ρ) ≫ K) a
  have h₂ := functorHomPostcomp_heq _ m hF hG
    (dgCellResolvedGraphPerfectNerveArrow_inclusion R B F G τ) ((ρ) ≫ K)
  have h₃ := functorHomPostcomp_postcomp
    (dgNerve.map (dgCellResolvedGraphModuleFunctor R B F))
    (dgNerve.map (dgCellResolvedGraphModuleFunctor R B G)) (ρ) K m
  exact h₀.trans ((heq_of_eq h₁).symm.trans (h₂.trans (heq_of_eq h₃).symm))

end SerrePositivity.KST.SConstruction
