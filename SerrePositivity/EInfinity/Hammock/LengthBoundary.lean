module

public import SerrePositivity.EInfinity.Hammock.ProperOverlap

/-!
# 長さ制限の包含の像の和としての元の境界

概要：短い語からの包含の像の和を境界とし、proper 性から前の段階への射を構成する。
方針：各単体の元の表示を選び、像の重なりの回収で選択に依存しないことを証明する。
規約：境界の添字図式の余極限と像の和を無証明に同一視しない。
使われ方：長さ濾過の段階の貼り合わせ。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w})

/-- 長さ n 以下の元の語の包含の像の和。 -/
def lengthBoundary (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : (F.obj c).Subcomplex :=
  ⨆ (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (_ha : a.length ≤ n) (f : a ⟶ c) (_hf : Function.Injective f.orderHom),
    Subfunctor.range (F.map f)

/-- 境界の単体を元の短い語から回収する表示。 -/
structure BoundaryPresentation (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (k : SimplexCategoryᵒᵖ)
    (x : (F.obj c).obj k) where
  source : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word
  bound : source.length ≤ n
  arrow : source ⟶ c
  injective : Function.Injective arrow.orderHom
  simplex : (F.obj source).obj k
  image : (F.map arrow).app k simplex = x

lemma lengthBoundary_mem_iff (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (k : SimplexCategoryᵒᵖ)
    (x : (F.obj c).obj k) :
    x ∈ (lengthBoundary F n c).obj k ↔ Nonempty (BoundaryPresentation F n c k x) := by
  simp only [lengthBoundary, Subfunctor.iSup_obj, Set.mem_iUnion, Subfunctor.range_obj,
    Set.mem_range]
  constructor
  · rintro ⟨a, ha, f, hf, σ, hσ⟩
    exact ⟨⟨a, ha, f, hf, σ, hσ⟩⟩
  · rintro ⟨p⟩
    exact ⟨p.source, p.bound, p.arrow, p.injective, p.simplex, p.image⟩

def boundaryPresentation (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (k : SimplexCategoryᵒᵖ)
    (x : ((lengthBoundary F n c).toFunctor).obj k) : BoundaryPresentation F n c k x.val :=
  Classical.choice ((lengthBoundary_mem_iff F n c k x.val).1 x.property)

variable {F} (hF : ProperDiagram F)

def lengthBoundaryStageValue (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word ⥤ SSet.{w}) (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (k : SimplexCategoryᵒᵖ)
    (x : ((lengthBoundary F n c).toFunctor).obj k) : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStage F n).obj k :=
  let p := boundaryPresentation F n c k x
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n p.source p.bound).app k p.simplex

include hF

lemma lengthBoundaryStageValue_eq (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (k : SimplexCategoryᵒᵖ)
    (x : ((lengthBoundary F n c).toFunctor).obj k) {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (ha : a.length ≤ n)
    (f : a ⟶ c) (hf : Function.Injective f.orderHom) (σ : (F.obj a).obj k)
    (hσ : (F.map f).app k σ = x.val) :
    lengthBoundaryStageValue F n c k x = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n a ha).app k σ := by
  let p := boundaryPresentation F n c k x
  exact hF.overlap_lengthStage p.arrow f p.injective hf n p.bound ha k p.simplex σ
    (p.image.trans hσ.symm)

/-- 元の境界の像の和から、元の短い語の余極限への射。 -/
def lengthBoundaryToStage (n : ℕ) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (lengthBoundary F n c).toFunctor ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStage F n where
  app k := ↾lengthBoundaryStageValue F n c k
  naturality k l α := by
    apply ConcreteCategory.hom_ext
    intro x
    let p := boundaryPresentation F n c k x
    have hm : (F.map p.arrow).app l ((F.obj p.source).map α p.simplex) =
        (((lengthBoundary F n c).toFunctor).map α x).val :=
      (NatTrans.naturality_apply (F.map p.arrow) α p.simplex).trans
        (congrArg ((F.obj c).map α) p.image)
    change lengthBoundaryStageValue F n c l (((lengthBoundary F n c).toFunctor).map α x) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStage F n).map α (lengthBoundaryStageValue F n c k x)
    rw [lengthBoundaryStageValue_eq hF n c l _ p.bound p.arrow p.injective _ hm,
      lengthBoundaryStageValue_eq hF n c k x p.bound p.arrow p.injective p.simplex p.image]
    exact NatTrans.naturality_apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n p.source p.bound) α p.simplex

/-- 境界の射と元の上の段階への標準射の可換四角形。 -/
lemma lengthBoundary_square {n m : ℕ} (h : n ≤ m) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (hc : c.length ≤ m) :
    lengthBoundaryToStage hF n c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition F h =
      (lengthBoundary F n c).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F m c hc := by
  apply NatTrans.ext
  funext k
  apply ConcreteCategory.hom_ext
  intro x
  let p := boundaryPresentation F n c k x
  have hl := congrArg (fun η => η.app k p.simplex)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_transition F h p.source p.bound)
  have hr := congrArg (fun η => η.app k p.simplex)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion_naturality F m (p.bound.trans h) hc p.arrow)
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition F h).app k
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F n p.source p.bound).app k p.simplex) = _ at hl
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F m c hc).app k ((F.map p.arrow).app k p.simplex) = _ at hr
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageTransition F h).app k (lengthBoundaryStageValue F n c k x) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lengthStageInclusion F m c hc).app k x.val
  rw [lengthBoundaryStageValue_eq hF n c k x p.bound p.arrow p.injective p.simplex p.image]
  rw [p.image] at hr
  exact hl.trans hr.symm

end SerrePositivity.EInfinity.Hammock
