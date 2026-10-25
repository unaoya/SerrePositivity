module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndImagePresentations
public import SerrePositivity.InfinityCategories.F2.Presentable.PiSmallFiltered
public import SerrePositivity.InfinityCategories.F2.Ind.CofinalUniverseLift

/-!
概要：小さい辺族の compact 表示を、同じ宇宙の一つの filtered 添字へ揃える。
方針：P-10 の公開共終添字を使い、各元の全普遍余錐を制限する。
規約：全余錐の元の頂点・普遍性・全項の compact 性を保持する。
使われ方：実 Ind 像の小さい余積閉性に向けた同期工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 小さい元の辺族は、共通 filtered 添字上の compact な全図式と元の普遍余錐を持つ。 -/
lemma indArrowImageFamily_hasCommonCompactPresentation
    (edges : I → C _⦋1⦌) (hC : HasSmallColimits C)
    (G : Ind.IndInfinity κ A ⟶ generatedArrowCategory edges)
    (hG : IsKappaAccessibleFunctor κ G)
    (hcompact : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} κ
      ((Ind.indYoneda κ A ≫ G ≫ generatedArrowInclusion edges).app _ (ULift.up a)))
    {B : Type u} (f : B → ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌)
    (hf : ∀ b, IndArrowImageVertex edges G (f b)) :
    ∃ (K : SSet.{u}) (_hK : Quasicategory K) (_hκ : IsKappaFiltered κ K)
      (D : B → ((SSet.uliftFunctor.{u + 1, u}).obj K ⟶ generatedArrowCategory edges))
      (c : ∀ b, JoinCocone (D b ≫ generatedArrowInclusion edges)),
      (∀ b, (c b).vertex = f b) ∧ (∀ b, IsColimitCone (c b)) ∧
      ∀ b k, Compact.IsKappaCompact.{u, u + 1} κ
        ((D b ≫ generatedArrowInclusion edges).app _ k) := by
  classical
  have hp := fun b ↦ indArrowImageVertex_hasCompactPresentation edges hC G hG hcompact (hf b)
  choose J hJ hκ d c hv hc hcomp using hp
  have := hJ
  have := hκ
  obtain ⟨K, hK, hκK, p, hp⟩ := exists_common_kappaFiltered_cofinal_index (κ := κ) J
  let r := fun b ↦ (SSet.uliftFunctor.{u + 1, u}).map (p b)
  refine ⟨K, hK, hκK, (fun b ↦ r b ≫ d b),
    (fun b ↦ (c b).restrict (r b)), ?_, ?_, ?_⟩
  · intro b
    exact (JoinCocone.vertex_restrict (c b) (r b)).trans (hv b)
  · intro b
    exact (Ind.isColimitCone_iff_restrict_rightCofinal (r b)
      (Ind.isRightCofinal_ulift (p b) (hp b)) (c b)).mp (hc b)
  · intro b k
    exact hcomp b ((r b).app _ k)

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
