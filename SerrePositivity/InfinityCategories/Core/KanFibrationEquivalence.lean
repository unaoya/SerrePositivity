module

public import SerrePositivity.InfinityCategories.Core.KanPrismLifting
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

/-!
概要：同値でもある Fibration は trivial Kan fibration。
方針：fiber 内の単位のホモトピーを境界上で使い、相対 prism を持ち上げる。
規約：モデル構造の弱同値や因子分解を使わない。
使われ方：HTT §2.2、Kerodon §4.8.4 の写像空間の可縮な fiber。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
  HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：quasicategory の同値でもある Fibration は全ての単射を持ち上げる。
方針：切断による境界の充填を fiber 内の単位で元の境界へ戻し、prism を相対充填する。
規約：同値は A3a の実際の逆射と可逆二胞体による。
使われ方：HTT §2.2、Kerodon §4.8.4 の写像空間の判定。 -/
lemma trivialKanFibration_of_fibration_of_isQCatEquivalence {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [Fibration p]
    (he : IsQCatEquivalence p) : TrivialKanFibration p := by
  obtain ⟨s, hs, k, hk⟩ := fibration_exists_section_and_relativeFunctorEdge p he
  let T := simplicialHomotopyOfFunctorEdge k
  let J := (β_ (Δ[1] : SSet.{u}) E).hom ≫ T.h
  have hJ₀ : prismEndpoint 0 E ≫ J = p ≫ s := by
    rw [← Category.assoc, prismEndpoint_zero_braiding]
    exact T.h₀
  have hJ₁ : prismEndpoint 1 E ≫ J = 𝟙 E := by
    rw [← Category.assoc, prismEndpoint_one_braiding]
    exact T.h₁
  have hJp : J ≫ p = snd (Δ[1] : SSet.{u}) E ≫ p := by
    rw [Category.assoc, simplicialHomotopyOfFunctorEdge_comp_eq_constant p p k hk,
      ← Category.assoc]
    rfl
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  let H := (Δ[1] ◁ a) ≫ J
  let F₀ := b ≫ s
  let b' := snd (Δ[1] : SSet.{u}) (Δ[n] : SSet.{u}) ≫ b
  have hF₀ : (boundary n).ι ≫ F₀ = prismEndpoint 0 (boundary n : SSet.{u}) ≫ H := by
    dsimp only [F₀, H]
    rw [← Category.assoc (prismEndpoint 0 (boundary n : SSet.{u})) (Δ[1] ◁ a) J,
      prismEndpoint_naturality, Category.assoc, hJ₀]
    change (boundary n).ι ≫ b ≫ s = a ≫ p ≫ s
    rw [← Category.assoc, ← sq.w, Category.assoc]
  have hH : H ≫ p = (Δ[1] ◁ (boundary n).ι) ≫ b' := by
    rw [Category.assoc, hJp]
    change ((Δ[1] : SSet.{u}) ◁ a) ≫ snd Δ[1] E ≫ p =
      (Δ[1] ◁ (boundary n).ι) ≫ snd Δ[1] Δ[n] ≫ b
    rw [← Category.assoc, whiskerLeft_snd, Category.assoc,
      ← Category.assoc (Δ[1] ◁ (boundary n).ι), whiskerLeft_snd, Category.assoc, sq.w]
  have hb : F₀ ≫ p = prismEndpoint 0 Δ[n] ≫ b' := by
    change (b ≫ s) ≫ p = prismEndpoint 0 Δ[n] ≫ (snd Δ[1] Δ[n] ≫ b)
    rw [Category.assoc, hs, Category.comp_id, ← Category.assoc]
    rfl
  obtain ⟨F, hF, _, hFp⟩ := fibration_lift_prism p (boundary n) H F₀ b' hF₀ hH hb
  refine CommSq.HasLift.mk' { l := prismEndpoint 1 Δ[n] ≫ F, fac_left := ?_, fac_right := ?_ }
  · rw [← Category.assoc (boundary n).ι (prismEndpoint 1 Δ[n]) F,
      ← prismEndpoint_naturality, Category.assoc, hF]
    change prismEndpoint 1 (boundary n : SSet.{u}) ≫ (Δ[1] ◁ a) ≫ J = a
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, hJ₁, Category.comp_id]
  · rw [Category.assoc, hFp]
    change prismEndpoint 1 Δ[n] ≫ (snd Δ[1] Δ[n] ≫ b) = b
    rw [← Category.assoc]
    rfl

/-- 概要：Kan 複体間の Fibration が実際の単体的ホモトピー逆を持てば trivial Kan fibration。
方針：Kan 複体の同値との比較を使い、相対的な単位による境界の充填へ戻す。
規約：π₀ の全単射だけを仮定する主張ではない。
使われ方：Kerodon §4.8.3–4.8.4 の写像空間の fiber の可縮性。 -/
lemma trivialKanFibration_of_fibration_of_simplicialHomotopyEquivalence {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (he : IsSimplicialHomotopyEquivalence p) : TrivialKanFibration p :=
  trivialKanFibration_of_fibration_of_isQCatEquivalence p he.isQCatEquivalence

end SerrePositivity.InfinityCategories
