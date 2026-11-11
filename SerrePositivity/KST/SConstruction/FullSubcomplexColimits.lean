module
public import SerrePositivity.KST.SConstruction.FullSubcomplexUniversalVertices
public import SerrePositivity.KST.SConstruction.TrivialFibrationUniversality
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-! # 全部分複体による余極限の反映
概要：全部分複体内の余錐が周囲で普遍なら、全部分複体内でも普遍。
方針：全頂点を含む射に対する包含の持ち上げ性を内部 Hom に移す。
規約：余極限の保存はここでは主張しない。使われ方：S_n 内の点ごとの cofiber 補完。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：内部 Hom の全部分複体包含も全頂点を含む射に対して持ち上げ性を持つ。
方針：tensor・内部 Hom 随伴で積の頂点全射性へ戻す。
規約：単射性・quasicategory 性は不要。使われ方：相対普遍性の反映。 -/
lemma ihom_fullSubcomplex_hasLiftingProperty_of_vertexSurjective {A B X : SSet.{u}}
    (K : SSet.{u}) (P : X _⦋0⦌ → Prop) (i : A ⟶ B)
    (hi : Function.Surjective (i.app (Opposite.op ⦋0⦌))) :
    HasLiftingProperty i ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι) := by
  apply ((ihom.adjunction K).hasLiftingProperty_iff i _).1
  apply fullSubcomplex_hasLiftingProperty_of_vertexSurjective
  rintro ⟨a, b⟩
  obtain ⟨c, hc⟩ := hi b
  exact ⟨(a, c), Prod.ext rfl hc⟩

/-- 概要：境界を持ち上げる包含と標的の単射を通じて相対始点境界充填を反映する。
方針：周囲で得た充填を元へ持ち上げ、標的の単射で可換性を反映する。
規約：quasicategory 性は不要。使われ方：全部分複体の余極限性の反映。 -/
lemma initialBoundaryLifting_reflect_of_boundary_lifting {E B E' B' : SSet.{u}}
    (p : E ⟶ B) (q : E' ⟶ B') (i : E ⟶ E') (j : B ⟶ B') [Mono j]
    (h : i ≫ q = p ≫ j)
    (hi : ∀ n : ℕ, HasLiftingProperty (boundary (n + 1)).ι i)
    {x : E _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting q (i.app (Opposite.op ⦋0⦌) x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting p x := by
  intro n a b ha sq
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ (a ≫ i) =
      SSet.yonedaEquiv.symm (i.app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, ha, SSet.yonedaEquiv_symm_comp]
  have cs : CommSq (a ≫ i) (boundary (n + 1)).ι q (b ≫ j) := by
    constructor
    rw [Category.assoc, h, ← Category.assoc, sq.w, Category.assoc]
  obtain ⟨F, hF, hFq⟩ := hx n _ _ hf cs
  have := hi n
  have cs' : CommSq a (boundary (n + 1)).ι i F := ⟨hF.symm⟩
  refine ⟨cs'.lift, cs'.fac_left, ?_⟩
  apply (cancel_mono j).1
  rw [Category.assoc, ← h, ← Category.assoc, cs'.fac_right, hFq]

/-- 概要：全部分複体内の余錐の周囲での余極限性を全部分複体へ反映する。
方針：余錐制限の相対始点境界充填を、内部 Hom の包含を通じて反映する。
規約：周囲だけが quasicategory。使われ方：gapped 普遍余錐を S_n 内で普遍にする。 -/
lemma isColimitCone_fullSubcomplex_of_ambient {K X : SSet.{u}} [Quasicategory X]
    (P : X _⦋0⦌ → Prop) {p : K ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u})}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι c)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_initialBoundaryLifting_coconeRestriction c
  apply initialBoundaryLifting_reflect_of_boundary_lifting
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K X) ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι) ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι)
  · exact (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}))).naturality _
  · intro n
    exact ihom_fullSubcomplex_hasLiftingProperty_of_vertexSurjective _ P _
      (boundary_vertex_surjective n)
  · exact hc.initialBoundaryLifting

end SerrePositivity.KST.SConstruction
