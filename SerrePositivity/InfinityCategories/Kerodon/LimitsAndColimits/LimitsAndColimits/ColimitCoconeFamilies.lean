module
public import Mathlib.CategoryTheory.LiftingProperties.Limits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRelativeBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundary
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.RelativeInitialVertices

/-! # 図式の族に沿う普遍余錐の選択

概要：各頂点で余極限が存在する図式の族に沿って、普遍余錐を coherent に選択できる。
方針：普遍余錐の全部分圏への射影を引き戻し、正次元の相対境界充填と零次元の存在を使う。
規約：基底に quasicategory 性や有限性は要求しない。
使われ方：S3 の suspension 図式の評価の同値性。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：普遍余錐全体からなる全部分単体集合。
方針：余錐制限の相対始対象を取る。
規約：quasicategory を値域とすると通常の余極限性に一致する。
使われ方：図式の族に沿う余極限の選択。 -/
def colimitCocones (K X : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X) : SSet.{u})

/-- 概要：普遍余錐の全部分単体集合は quasicategory。
方針：関手 quasicategory の全部分複体のホーン充填を用いる。
規約：X は quasicategory、K は任意。
使われ方：普遍余錐の族のホモトピー圏。 -/
instance colimitCocones_quasicategory (K X : SSet.{u}) [Quasicategory X] :
    Quasicategory (colimitCocones K X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 概要：余錐の頂点は、この全部分圏の頂点条件を満たすことと余極限性が同値。
方針：相対始点境界充填の判定を使う。
規約：X は quasicategory。
使われ方：普遍余錐の全部分圏と coslice による定義の照合。 -/
lemma colimitCocones_vertex_iff {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_initialBoundaryLifting c).symm

/-- 概要：普遍余錐全体から図式への射影。
方針：全部分圏の包含と余錐の制限を合成する。
規約：高次単体でも元の図式の族を保つ。
使われ方：余極限の選択の基底となる射。 -/
def colimitCoconeProjection (K X : SSet.{u}) : colimitCocones K X ⟶ (ihom K).obj X :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X)

/-- 概要：図式の族に沿った普遍余錐の射影は、各頂点で余極限があれば trivial Kan fibration。
方針：正次元は相対境界充填の引き戻し、零次元は与えられた余極限の存在で持ち上げる。
規約：基底 A は任意。値域 X の quasicategory 性のみを要求する。
使われ方：S3 の図式の族の普遍余錐の coherent な選択。 -/
lemma colimitCoconeProjection_pullback_trivialKanFibration {A K X : SSet.{u}}
    [Quasicategory X] (d : A ⟶ (ihom K).obj X)
    (hd : ∀ a : A _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).symm (d.app (Opposite.op ⦋0⦌) a))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (pullback.snd (colimitCoconeProjection K X) d) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  cases n with
  | zero =>
    constructor
    intro a b sq
    let v := SSet.yonedaEquiv b
    obtain ⟨c, hc⟩ := hd v
    let w : (colimitCocones K X) _⦋0⦌ := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c.val, by
      intro α
      have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
      exact hc.initialBoundaryLifting⟩
    have hw : (colimitCoconeProjection K X).app (Opposite.op ⦋0⦌) w =
        d.app (Opposite.op ⦋0⦌) v := by
      change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ c.val) = _
      rw [c.property]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).apply_symm_apply _
    let g : (Δ[0] : SSet.{u}) ⟶ pullback (colimitCoconeProjection K X) d :=
      pullback.lift (SSet.yonedaEquiv.symm w) b (by
        apply SSet.yonedaEquiv.injective
        rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, SSet.yonedaEquiv_comp]
        exact hw)
    exact CommSq.HasLift.mk' {
      l := g
      fac_left := boundary.hom_ext₀
      fac_right := pullback.lift_snd _ _ _ }
  | succ n =>
    have : HasLiftingProperty (boundary (n + 1)).ι (colimitCoconeProjection K X) :=
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.relativeInitialProjection_hasLiftingProperty_boundary (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X) n
    infer_instance

/-- 概要：各頂点で余極限を持つ図式の族には、全単体に自然な普遍余錐の族がある。
方針：引き戻した trivial Kan fibration の厳密な切断を取る。
規約：図式への制限は厳密に元の族と一致する。
使われ方：S3 の余極限の関手的な選択。 -/
lemma exists_colimitCoconeFamily {A K X : SSet.{u}} [Quasicategory X]
    (d : A ⟶ (ihom K).obj X)
    (hd : ∀ a : A _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).symm (d.app (Opposite.op ⦋0⦌) a))) :
    ∃ f : A ⟶ colimitCocones K X, f ≫ colimitCoconeProjection K X = d := by
  have := colimitCoconeProjection_pullback_trivialKanFibration d hd
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section
    (pullback.snd (colimitCoconeProjection K X) d)
  refine ⟨s ≫ pullback.fst (colimitCoconeProjection K X) d, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]

/-- 概要：同じ図式の族の二つの普遍余錐の選択は関手として同型。
方針：引き戻した射の同じ切断上の持ち上げを比較し、普遍余錐の部分圏へ写す。
規約：基底に quasicategory 性は不要。比較は全単体に自然。
使われ方：S3 の余極限の選択の自然な比較。 -/
noncomputable def colimitCoconeFamilyIso {A K X : SSet.{u}} [Quasicategory X]
    (d : A ⟶ (ihom K).obj X)
    (hd : ∀ a : A _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K X).symm (d.app (Opposite.op ⦋0⦌) a)))
    (f g : A ⟶ colimitCocones K X)
    (hf : f ≫ colimitCoconeProjection K X = d)
    (hg : g ≫ colimitCoconeProjection K X = d) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g := by
  have := colimitCoconeProjection_pullback_trivialKanFibration d hd
  let f' := pullback.lift f (𝟙 A) (hf.trans (Category.id_comp d).symm)
  let g' := pullback.lift g (𝟙 A) (hg.trans (Category.id_comp d).symm)
  have he : f' ≫ pullback.snd (colimitCoconeProjection K X) d =
      g' ≫ pullback.snd (colimitCoconeProjection K X) d := by
    simp only [f', g', pullback.lift_snd]
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorIsoOfTrivialKanFibration (pullback.snd (colimitCoconeProjection K X) d) f' g' he)
    (pullback.fst (colimitCoconeProjection K X) d)
  simpa only [f', g', pullback.lift_fst] using e

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
