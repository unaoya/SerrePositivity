module

public import SerrePositivity.AlgebraicGeometry.ProperInductiveLevelBaseChange

/-!
概要：帰納的レベルの Cartesian 移送と有限表示 nilimmersion の消去。
方針：実際の pullback の同型と、選んだ nilimmersion の合成を使う。
規約：レベルの存在・元の射の固有性を追加仮定にして置き換えない。
使われ方：G3 の被約化の後のレベルから元の射へ戻す接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u
namespace ProperInductiveLevel

/-- 任意の Cartesian な正方形で帰納的レベルを移す。 -/
theorem of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {a : X' ⟶ X} {f' : X' ⟶ Y'} (H : IsPullback a f' f g) {n : ℕ}
    (hf : ProperInductiveLevel n f) : ProperInductiveLevel n f' := by
  have h := (iso_source_iff H.isoPullback (pullback.snd f g) n).mpr
    (baseChange f g hf)
  simpa only [H.isoPullback_hom_snd] using h

/-- 選んだ nilimmersion をさらに合成してレベルを保つ。 -/
theorem comp_nilimmersion {X Y Z : Scheme.{u}} {f : X ⟶ Y} {n : ℕ}
    (hf : ProperInductiveLevel n f) (i : Y ⟶ Z)
    [IsClosedImmersion i] [Surjective i] [LocallyOfFinitePresentation i] :
    ProperInductiveLevel n (f ≫ i) := by
  cases n with
  | zero =>
    obtain ⟨X', Y', j, q, a, hj, hjs, hjf, hq, hqf, hqs, hqfp, ha⟩ := hf
    letI := hj
    letI := hjs
    letI := hjf
    exact ⟨X', Y', j ≫ i, q, a, inferInstance, inferInstance, inferInstance,
      hq, hqf, hqs, hqfp, by rw [← Category.assoc, ha, Category.assoc]⟩
  | succ n =>
    obtain ⟨X', X₀, Y₀, j, r, q, a, J, hj, hjs, hjf, hr, hrs, hrf, hJ, hIso,
      hn, hq, hqf, hqs, hqfp, ha⟩ := hf
    letI := hj
    letI := hjs
    letI := hjf
    refine ⟨X', X₀, Y₀, j ≫ i, r, q, a, J, inferInstance, inferInstance, inferInstance,
      hr, hrs, hrf, hJ, hIso, hn, hq, hqf, hqs, hqfp, ?_⟩
    rw [← Category.assoc, ha]
    simp only [Category.assoc]

/-- nilimmersion 上の底変換に得たレベルを、元の射へ戻す。 -/
theorem of_nilimmersion_baseChange {X Y T : Scheme.{u}} (f : X ⟶ Y) (i : T ⟶ Y)
    [IsClosedImmersion i] [Surjective i] [LocallyOfFinitePresentation i] {n : ℕ}
    (hf : ProperInductiveLevel n (pullback.snd f i)) : ProperInductiveLevel n f :=
  (hf.comp_nilimmersion i).of_refinement (pullback.fst f i) f pullback.condition

end ProperInductiveLevel
end SerrePositivity.AlgebraicGeometry
