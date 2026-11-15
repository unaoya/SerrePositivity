module

public import SerrePositivity.AlgebraicGeometry.CartesianCompositeStageLimit
public import SerrePositivity.AlgebraicGeometry.FiniteStageMorphisms

/-!
概要：有限個の元の射を、同じ係数段の両模型の底変換の間の実際の射へ降ろす。
方針：固定した有限表示の標的への因子化と、基底上の可換式から pullback lift を作る。
規約：段の基底への可換式と元の射との合成式を保持する。
使われ方：G2 の重なりの反転・対角の逆・三重交叉の射の同時降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v
variable {J : Type u} [SmallCategory J]

/-- 合成係数の底変換図式から、固定した係数基底への構造射の自然変換。 -/
def compositeStageStructureMap (D : J ⥤ Scheme.{u}) (i : J)
    {S Y : Scheme.{u}} (γ : D.obj i ⟶ S) (p : Y ⟶ S) :
    compositeStageBaseChangeDiagram D i γ p ⟶ (Functor.const (Over i)).obj S where
  app j := pullback.snd (D.map j.hom ≫ γ) p ≫ p
  naturality {j k} q := by
    simp [compositeStageBaseChangeDiagram, Over.post, Over.map, Over.pullback, Category.assoc]

/-- 有限個の元の射を、一つの共通する係数段の両模型の底変換の間の射へ降ろす。 -/
theorem exists_finite_compositeStage_maps_of_isLimit [IsCofiltered J]
    (D : J ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i : J)
    [∀ {b d} (q : b ⟶ d), IsAffineHom (D.map q)]
    [∀ b, CompactSpace (D.obj b)] [∀ b, QuasiSeparatedSpace (D.obj b)]
    {S : Scheme.{u}} (γ : D.obj i ⟶ S) (g : c.pt ⟶ S) (hγ : c.π.app i ≫ γ = g)
    {ι : Type v} [Finite ι]
    (Y₀ Y X₀ : ι → Scheme.{u}) (q : ∀ a, Y₀ a ⟶ S) (p : ∀ a, X₀ a ⟶ S)
    [∀ a, QuasiCompact (q a)] [∀ a, QuasiSeparated (q a)]
    [∀ a, LocallyOfFinitePresentation (p a)]
    (b : ∀ a, Y a ⟶ Y₀ a) (x : ∀ a, Y a ⟶ c.pt)
    (hpb : ∀ a, IsPullback (b a) (x a) (q a) g)
    (l : ∀ a, Y a ⟶ X₀ a) (hl : ∀ a, l a ≫ p a = x a ≫ g) :
    ∃ (j : Over i)
      (f : ∀ a, pullback (D.map j.hom ≫ γ) (q a) ⟶ pullback (D.map j.hom ≫ γ) (p a)),
      ∀ a, f a ≫ pullback.fst (D.map j.hom ≫ γ) (p a) =
          pullback.fst (D.map j.hom ≫ γ) (q a) ∧
        (cartesianCompositeStageCone D c i γ (q a) g hγ (b a) (x a) (hpb a)).π.app j ≫
          f a ≫ pullback.snd (D.map j.hom ≫ γ) (p a) = l a := by
  let E (a : ι) := compositeStageBaseChangeDiagram D i γ (q a)
  let e (a : ι) := cartesianCompositeStageCone D c i γ (q a) g hγ (b a) (x a) (hpb a)
  let t (a : ι) := compositeStageStructureMap D i γ (q a)
  have he (a : ι) : IsLimit (e a) :=
    isLimit_cartesianCompositeStageCone D c i γ (q a) g hγ (b a) (x a) (hpb a) hc
  haveI (a : ι) (j : Over i) : CompactSpace ((E a).obj j) := by dsimp [E]; infer_instance
  haveI (a : ι) (j : Over i) : QuasiSeparatedSpace ((E a).obj j) := by dsimp [E]; infer_instance
  haveI (a : ι) {j k : Over i} (f : j ⟶ k) : IsAffineHom ((E a).map f) := by
    dsimp [E]; infer_instance
  have ht (a : ι) : (e a).π ≫ t a = (Functor.const (Over i)).map (l a ≫ p a) := by
    ext j
    change (e a).π.app j ≫ pullback.snd (D.map j.hom ≫ γ) (q a) ≫ q a = l a ≫ p a
    rw [← Category.assoc, cartesianCompositeStageCone_π_snd, (hpb a).w, hl]
  obtain ⟨j, s, hs⟩ := exists_finite_stage_maps_of_isLimit E t X₀ p e he l ht
  have hcomm (a : ι) : pullback.fst (D.map j.hom ≫ γ) (q a) ≫ (D.map j.hom ≫ γ) = s a ≫ p a := by
    rw [(hs a).2]
    exact pullback.condition
  refine ⟨j, fun a ↦ pullback.lift (pullback.fst (D.map j.hom ≫ γ) (q a)) (s a) (hcomm a), ?_⟩
  intro a
  refine ⟨by simp, ?_⟩
  simpa only [Category.assoc, pullback.lift_snd] using (hs a).1

end SerrePositivity.AlgebraicGeometry
