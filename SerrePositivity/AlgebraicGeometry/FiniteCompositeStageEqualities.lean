module

public import SerrePositivity.AlgebraicGeometry.BaseChangedModelArrow
public import SerrePositivity.AlgebraicGeometry.FiniteCompositeStageMaps

/-!
概要：元の極限で成立する有限個の模型間の等式を、同じ段の実際の底変換射の等式へ移す。
方針：Cartesian な源を頂点に保つ極限上で固定標的への一致判定を用い、二射影で戻す。
規約：係数射の忠実平坦性や単射性を仮定しない。
使われ方：G2 の gluing datum の六種の式を同時に満たす有限段。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v

/-- 元の極限で一致する有限個の二射は、一つの後の段で実際の底変換射として全て一致する。 -/
theorem exists_finite_compositeStage_equalities_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
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
    (l r : ∀ a, Y₀ a ⟶ X₀ a)
    (hl : ∀ a, l a ≫ p a = q a) (hr : ∀ a, r a ≫ p a = q a)
    (hab : ∀ a, b a ≫ l a = b a ≫ r a) :
    ∃ j : Over i, ∀ a,
      baseChangedModelArrow (D.map j.hom ≫ γ) (q a) (p a) (l a) (hl a) =
        baseChangedModelArrow (D.map j.hom ≫ γ) (q a) (p a) (r a) (hr a) := by
  let E (a : ι) := compositeStageBaseChangeDiagram D i γ (q a)
  let e (a : ι) := cartesianCompositeStageCone D c i γ (q a) g hγ (b a) (x a) (hpb a)
  let t (a : ι) := compositeStageStructureMap D i γ (q a)
  have he (a : ι) : IsLimit (e a) :=
    isLimit_cartesianCompositeStageCone D c i γ (q a) g hγ (b a) (x a) (hpb a) hc
  haveI (a : ι) (j : Over i) : CompactSpace ((E a).obj j) := by dsimp [E]; infer_instance
  haveI (a : ι) (j : Over i) : QuasiSeparatedSpace ((E a).obj j) := by dsimp [E]; infer_instance
  haveI (a : ι) {j k : Over i} (f : j ⟶ k) : IsAffineHom ((E a).map f) := by
    dsimp [E]; infer_instance
  let j₀ : Over i := Over.mk (𝟙 i)
  let a₀ (s : ι) : (E s).obj j₀ ⟶ X₀ s := pullback.snd (D.map j₀.hom ≫ γ) (q s) ≫ l s
  let b₀ (s : ι) : (E s).obj j₀ ⟶ X₀ s := pullback.snd (D.map j₀.hom ≫ γ) (q s) ≫ r s
  have ha₀ (s : ι) : (t s).app j₀ = a₀ s ≫ p s := by
    change pullback.snd _ (q s) ≫ q s = (pullback.snd _ (q s) ≫ l s) ≫ p s
    rw [Category.assoc, hl]
  have hb₀ (s : ι) : (t s).app j₀ = b₀ s ≫ p s := by
    change pullback.snd _ (q s) ≫ q s = (pullback.snd _ (q s) ≫ r s) ≫ p s
    rw [Category.assoc, hr]
  have hab₀ (s : ι) : (e s).π.app j₀ ≫ a₀ s = (e s).π.app j₀ ≫ b₀ s := by
    simpa only [a₀, b₀, e, ← Category.assoc, cartesianCompositeStageCone_π_snd] using hab s
  obtain ⟨j, f, hf⟩ := exists_finite_stage_equalities_of_isLimit E t X₀ p e he a₀ b₀ ha₀ hb₀ hab₀
  refine ⟨j, ?_⟩
  intro a
  apply (baseChangedModelArrow_eq_iff _ _ _ _ _ _ _).2
  simpa [a₀, b₀, E, compositeStageBaseChangeDiagram, Over.post, Over.map, Over.pullback,
    Category.assoc] using hf a

end SerrePositivity.AlgebraicGeometry
