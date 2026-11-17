module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingSimplex

/-!
概要：元の射の可換四角形から、交差射の基点変更と全再添字付けの等式を得る。
方針：同じ交差射の両側の合成則と、元の同じ対角射の自然性を使う。
規約：IS-W2 R03dの合成・自然性の法則。零番以外の新しい射を選ばない。
使われ方：長い単体が任意の面・退化に厳密に自然であることの交差部分。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open CategoryTheory
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  (A : I ⥤ Cᵒᵖ) (B : I ⥤ C) (h : ∀ i, (A.obj i).unop ⟶ B.obj i)
  (hh : ∀ {i j} (f : i ⟶ j), (A.map f).unop ≫ h i ≫ B.map f = h j)
  {n : ℕ} (σ : Fin (n+1) ⥤ I)

include hh

/-- 対角の交差射は、元の同じ射そのもの。 -/
theorem twistedPairingCross_diagonal (i : Fin (n+1)) :
    twistedPairingCross A B h σ i i = h (σ.obj i) :=
  hh (σ.map (homOfLE (Fin.zero_le i)))

/-- 両端以前の任意の同じ基点からも、同じ交差射を計算できる。 -/
theorem twistedPairingCross_changeBase (p a b : Fin (n+1)) (hpa : p ≤ a) (hpb : p ≤ b) :
    twistedPairingCross A B h σ a b =
      (A.map (σ.map (homOfLE hpa))).unop ≫ h (σ.obj p) ≫ B.map (σ.map (homOfLE hpb)) := by
  calc
    _ = twistedPairingCross A B h σ a p ≫ B.map (σ.map (homOfLE hpb)) :=
      (twistedPairingCross_right A B h σ a p b hpb).symm
    _ = ((A.map (σ.map (homOfLE hpa))).unop ≫ twistedPairingCross A B h σ p p) ≫
        B.map (σ.map (homOfLE hpb)) :=
      congrArg (fun f => f ≫ B.map (σ.map (homOfLE hpb)))
        (twistedPairingCross_left A B h σ a p p hpa).symm
    _ = _ := by rw [twistedPairingCross_diagonal A B h hh σ p, Category.assoc]

/-- 同じ交差射は、面・退化を含む全順序射の再添字付けに厳密に自然。 -/
theorem twistedPairingCross_reindex {m : ℕ} (α : Fin (m+1) →o Fin (n+1))
    (a b : Fin (m+1)) :
    twistedPairingCross A B h (α.monotone.functor ⋙ σ) a b =
      twistedPairingCross A B h σ (α a) (α b) := by
  have hc := (twistedPairingCross_changeBase A B h hh σ (α 0) (α a) (α b)
    (α.monotone (Fin.zero_le a)) (α.monotone (Fin.zero_le b))).symm
  simpa only [twistedPairingCross, Functor.comp_obj, Functor.comp_map, Monotone.functor] using hc

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
