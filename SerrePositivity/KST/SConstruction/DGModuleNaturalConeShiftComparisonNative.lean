module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeShiftComparisonIso
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInvNative

/-!
概要：同じ元 cone shift 逆同型を native 全関手同型へ接続する。
方針：元閉成分の実同型回収で全頂点の可逆性を示す。
規約：元の全ホモトピーと同じ cone shift 同型を保持する。
使われ方：実逆回転後の合成全比較の逆 shift 因子。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
private lemma actualCompositeIso {A B C : ModuleCategory R D}
    (e : A ≅ B) (d : B ≅ C) (f : A ⟶ C) (h : f = e.hom ≫ d.hom) : IsIso f := by
  rw [h]
  infer_instance
variable {P : Type (max (u + 1) v)} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
local notation "CF" => dgModuleNaturalConeFunctor R D F G η
local notation "S" => moduleShiftDG R D
local notation "CS" => fun s : ℤ => dgModuleNaturalConeFunctor R D (F.comp (S s)) (G.comp (S s))
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η (S s))
local notation "θ" => dgModuleNaturalConeShiftComparison R D F G η

/-- 概要：同じ cone shift 全比較の閉成分は K(D) で可逆。
方針：元入力同型と元実 cone shift 逆同型の同じ合成を使う。
規約：同じ実成分を保持。使われ方：native 全比較の頂点可逆性。 -/
lemma dgModuleNaturalConeShiftComparison_isIso (s : ℤ) (x : P) :
    IsIso ((moduleToHomotopy R D).map
      (dgModuleNaturalConeArrow R D (CS s) ((CF).comp (S s)) (θ s) x)) := by
  haveI : IsIso (dgModuleNaturalConeArrow R D (CS s) ((CF).comp (S s)) (θ s) x) :=
    actualCompositeIso R D (dgModuleNaturalConeShiftComparisonInputIso R D F G η s x)
    (moduleConeShiftIso R D s (dgModuleNaturalConeArrow R D F G η x)).symm
    (dgModuleNaturalConeArrow R D (CS s) ((CF).comp (S s)) (θ s) x)
    (dgModuleNaturalConeShiftComparison_arrow R D F G η s x)
  exact (moduleToHomotopy R D).map_isIso
    (dgModuleNaturalConeArrow R D (CS s) ((CF).comp (S s)) (θ s) x)

/-- 概要：元全 cone shift ホモトピーは全頂点で可逆。
方針：同じ閉成分の回収と元実加群同型を使う。
規約：元ホモトピーを保持。使われ方：全関手同型への束ね。 -/
lemma dgModuleNaturalConeShiftComparison_pointwise (s : ℤ)
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R P) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (θ s).homotopy z).toTruncated := by
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
  let a := dgModuleNaturalConeArrow R D (CS s) ((CF).comp (S s)) (θ s) x
  have hc : (θ s).app x = cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) a) := by
    apply Subtype.ext
    exact (dgModuleNaturalConeArrow_cycle R D (CS s) ((CF).comp (S s)) (θ s) x).symm
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_homotopy_vertex_edge (θ s) x
  rw [hc] at he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
  haveI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_isIso_of_homotopy R D a
    (dgModuleNaturalConeShiftComparison_isIso R D F G η s x)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
    (SSet.Truncated.HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R D a).toTruncated)

/-- 概要：同じ元 cone shift 逆比較の native 全関手同型。
方針：元全厳密比較の全ホモトピーと実同型成分を束ねる。
規約：元指定 cone shift 同型を使用。使われ方：実逆回転後の全比較の shift 因子。 -/
def dgModuleNaturalConeShiftComparisonNerveComparison (s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (CS s)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((CF).comp (S s))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (θ s).homotopy
    (dgModuleNaturalConeShiftComparison_pointwise R D F G η s)
end SerrePositivity.KST.SConstruction
