module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.CompactTailFactorization
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.SequentialPieces
public import SerrePositivity.InfinityCategories.F2.Presentable.CompStructCocone

/-!
概要：元の二表示の指定開始点から、同じ大域余錐へ向かう実比較三角形を構成する。
方針：左表示の compact 頂点からの元の脚を、右表示の開始点の後へ因子化する。
規約：両表示の大域頂点の一致を保持し、その compact 性を要求しない。
使われ方：HTT 5.5.4.13 の交互比較の初期辺と初期全余錐。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits Compact

/-- 小さい種集合は、元の同じ filtered poset 内の一つの開始点で支配できる。 -/
lemma exists_sequentialSeed_bound {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {A : Type u} [Preorder A] [IsCardinalFiltered A κ]
    (seed : Set A) (hseed : HasCardinalLT seed κ) :
    ∃ a : A, ∀ x ∈ seed, x ≤ a := by
  obtain ⟨a, ⟨h⟩⟩ := IsCardinalFiltered.exists_max (κ := κ)
    (fun x : seed ↦ x.val) hseed
  exact ⟨a, fun x hx ↦ leOfHom (h ⟨x, hx⟩)⟩

/-- 二表示の指定開始点から、右開始点の後に元の二脚を結ぶ実三角形が存在する。 -/
lemma compactPresentations_initialTriangle {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {C : SSet.{u + 1}} [Quasicategory C] {I₀ I₁ : SSet.{u}}
    [Quasicategory I₁] [IsKappaFiltered κ I₁]
    (D₀ : (SSet.uliftFunctor.{u + 1, u}).obj I₀ ⟶ C)
    (D₁ : (SSet.uliftFunctor.{u + 1, u}).obj I₁ ⟶ C)
    (c₀ : JoinCocone D₀) (c₁ : JoinCocone D₁) (hc₁ : IsColimitCone c₁)
    (hv : c₀.vertex = c₁.vertex) (a : I₀ _⦋0⦌) (b : I₁ _⦋0⦌)
    (ha : IsKappaCompact.{u, u + 1} κ (D₀.app _ (ULift.up a))) :
    ∃ j : (sliceUnder (SSet.yonedaEquiv.symm b)) _⦋0⦌,
      ∃ f : C.Edge (D₀.app _ (ULift.up a))
        (D₁.app _ (ULift.up (JoinCocone.vertex (p := SSet.yonedaEquiv.symm b) j))),
      ∃ T : f.CompStruct (coconeTransportLeg c₁
          (ULift.up (JoinCocone.vertex (p := SSet.yonedaEquiv.symm b) j)))
        ((coconeTransportLeg c₀ (ULift.up a)).ofEq rfl hv),
        (compStructCocone T).vertex = c₁.vertex := by
  obtain ⟨j, f, ⟨T⟩⟩ := compactSource_factorization_after_point ha D₁ c₁ hc₁ b
    ((coconeTransportLeg c₀ (ULift.up a)).ofEq rfl hv)
  exact ⟨j, f, T, compStructCocone_vertex T⟩

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
