module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetNerve

/-!
概要：元の小さい coherent nerve 図式を、同じ小さい filtered 部分 poset へ因子化する。
方針：頂点像を小さい filtered 部分集合へ拡大し、自然性から全鎖を部分型へ持ち上げる。
規約：合成は元の図式と全単体で厳密に等しい。頂点ごとの同値だけでは済ませない。
使われ方：濃度変更の小さい部分表示を、元の図式の制限として扱う。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {I : Type u} [Preorder I] {K : SSet.{u}}

/-- 元の部分 poset の包含関手。 -/
def subsetInclusion (A : Set I) : A ⥤ I where
  obj x := x.val
  map f := homOfLE (leOfHom f)

instance nerveMap_subsetInclusion_mono (A : Set I) : Mono (nerveMap (subsetInclusion A)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro n
  rw [mono_iff_injective]
  intro a b hab
  change a ⋙ subsetInclusion A = b ⋙ subsetInclusion A at hab
  exact CategoryTheory.Functor.ext
    (fun i ↦ Subtype.ext (Functor.congr_obj hab i)) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 部分集合の包含が与える、同じ元の poset 上の遷移。 -/
def subsetTransition {A B : Set I} (hAB : A ⊆ B) : A ⥤ B where
  obj x := ⟨x.val, hAB x.property⟩
  map f := homOfLE (leOfHom f)

/-- 遷移は元の poset への包含を厳密に保つ。 -/
lemma nerveMap_subsetTransition_inclusion {A B : Set I} (hAB : A ⊆ B) :
    nerveMap (subsetTransition hAB) ≫ nerveMap (subsetInclusion B) =
      nerveMap (subsetInclusion A) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 全頂点が部分集合に入るなら、元の全 coherent 図式をその部分集合へ持ち上げる。 -/
def nerveSubsetLift (a : K ⟶ nerve I) (A : Set I)
    (ha : ∀ v : K _⦋0⦌, (a.app _ v).obj 0 ∈ A) : K ⟶ nerve A where
  app n := ↾fun s ↦
    { obj j := ⟨(a.app n s).obj j, by
        have hh := ha (K.map (SimplexCategory.const ⦋0⦌ n.unop j).op s)
        have hn := ConcreteCategory.congr_hom
          (a.naturality (SimplexCategory.const ⦋0⦌ n.unop j).op) s
        change a.app _ (K.map (SimplexCategory.const ⦋0⦌ n.unop j).op s) =
          (nerve I).map (SimplexCategory.const ⦋0⦌ n.unop j).op (a.app n s) at hn
        rw [hn] at hh
        exact hh⟩
      map f := homOfLE (leOfHom ((a.app n s).map f)) }
  naturality {n m} β := by
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun j ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    apply Subtype.ext
    have hn := ConcreteCategory.congr_hom (a.naturality β) s
    change a.app m (K.map β s) = (nerve I).map β (a.app n s) at hn
    exact congrArg (fun q ↦ q.obj j) hn

/-- 包含との合成は元の全図式そのもの。 -/
lemma nerveSubsetLift_inclusion (a : K ⟶ nerve I) (A : Set I)
    (ha : ∀ v : K _⦋0⦌, (a.app _ v).obj 0 ∈ A) :
    nerveSubsetLift a A ha ≫ nerveMap (subsetInclusion A) = a := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change ((nerveSubsetLift a A ha).app n s) ⋙ subsetInclusion A = a.app n s
  exact CategoryTheory.Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ Subsingleton.elim _ _)

/-- 元の全図式の持ち上げは、部分集合を大きくする遷移と厳密に整合する。 -/
lemma nerveSubsetLift_transition (a : K ⟶ nerve I) {A B : Set I} (hAB : A ⊆ B)
    (ha : ∀ v : K _⦋0⦌, (a.app _ v).obj 0 ∈ A) :
    nerveSubsetLift a A ha ≫ nerveMap (subsetTransition hAB) =
      nerveSubsetLift a B (fun v ↦ hAB (ha v)) := by
  apply (cancel_mono (nerveMap (subsetInclusion B))).mp
  rw [Category.assoc, nerveMap_subsetTransition_inclusion,
    nerveSubsetLift_inclusion, nerveSubsetLift_inclusion]

/-- μ-small な元の coherent 図式は、小さい κ-filtered 部分添字を厳密に通る。 -/
lemma exists_smallFilteredPiece_factorization {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {I : Type u} [PartialOrder I] [IsCardinalFiltered I κ]
    {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K) (a : K ⟶ nerve I) :
    ∃ (A : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I) (b : K ⟶ nerve A.val),
      b ≫ nerveMap (subsetInclusion A.val) = a ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (nerve A.val) ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (nerve A.val) := by
  let f : K _⦋0⦌ → I := fun v ↦ (a.app _ v).obj 0
  have hV : HasCardinalLT (K _⦋0⦌) μ :=
    (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.cardinal_vertices_lt_of_isKappaSmall hK)
  have hA : HasCardinalLT (Set.range f) μ :=
    hV.of_surjective (fun v ↦ ⟨f v, Set.mem_range_self v⟩) (by
      rintro ⟨i, v, rfl⟩
      exact ⟨v, rfl⟩)
  obtain ⟨A, hA⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_smallFilteredPiece_containing h (Set.range f) hA
  have ha : ∀ v : K _⦋0⦌, (a.app _ v).obj 0 ∈ A.val :=
    fun v ↦ hA (Set.mem_range_self v)
  exact ⟨A, nerveSubsetLift a A.val ha, nerveSubsetLift_inclusion a A.val ha,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFilteredPiece_nerve_properties h A⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
