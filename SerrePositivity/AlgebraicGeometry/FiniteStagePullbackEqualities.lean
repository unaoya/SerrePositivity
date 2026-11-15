module

public import SerrePositivity.AlgebraicGeometry.FiniteStageMorphisms

/-!
概要：固定模型への射影の有限個の一致を、底変換模型への実際の射の一致へ戻す。
方針：基底座標を保ったまま固定模型への一致判定を同じ段へそろえ、二射影で判定する。
規約：底変換射の単射性や忠実平坦性を仮定しない。
使われ方：G2 の反転の逆・対角・cocycle の有限個の式。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v

/-- 基底座標が同じ二つの射の固定模型への射影が極限で一致すれば、同じ後の段で全て一致。 -/
theorem exists_finite_stage_pullback_equalities_of_isLimit
    {J : Type u} [SmallCategory J] [IsCofiltered J]
    {ι : Type v} [Finite ι] {S B : Scheme.{u}} (γ : B ⟶ S)
    (D : ι → J ⥤ Scheme.{u}) (t : ∀ e, D e ⟶ (Functor.const J).obj S)
    (X : ι → Scheme.{u}) (p : ∀ e, X e ⟶ S)
    (c : ∀ e, Cone (D e)) (hc : ∀ e, IsLimit (c e))
    [∀ e, LocallyOfFinitePresentation (p e)]
    [∀ e {i j} (q : i ⟶ j), IsAffineHom ((D e).map q)]
    [∀ e i, CompactSpace ((D e).obj i)] [∀ e i, QuasiSeparatedSpace ((D e).obj i)]
    {i : J} (a b : ∀ e, (D e).obj i ⟶ pullback γ (p e))
    (ha : ∀ e, (t e).app i = (a e ≫ pullback.snd γ (p e)) ≫ p e)
    (hbase : ∀ e, a e ≫ pullback.fst γ (p e) = b e ≫ pullback.fst γ (p e))
    (hab : ∀ e, (c e).π.app i ≫ a e ≫ pullback.snd γ (p e) =
      (c e).π.app i ≫ b e ≫ pullback.snd γ (p e)) :
    ∃ (j : J) (q : j ⟶ i), ∀ e, (D e).map q ≫ a e = (D e).map q ≫ b e := by
  have hb (e : ι) : (t e).app i = (b e ≫ pullback.snd γ (p e)) ≫ p e := by
    rw [ha e, Category.assoc, ← pullback.condition, ← Category.assoc,
      hbase e, Category.assoc, pullback.condition, ← Category.assoc]
  obtain ⟨j, q, hq⟩ := exists_finite_stage_equalities_of_isLimit D t X p c hc
    (fun e ↦ a e ≫ pullback.snd γ (p e)) (fun e ↦ b e ≫ pullback.snd γ (p e))
    ha hb (fun e ↦ by simpa only [Category.assoc] using hab e)
  refine ⟨j, q, ?_⟩
  intro e
  apply pullback.hom_ext
  · simpa only [Category.assoc] using congrArg (fun z ↦ (D e).map q ≫ z) (hbase e)
  · simpa only [Category.assoc] using hq e

end SerrePositivity.AlgebraicGeometry
