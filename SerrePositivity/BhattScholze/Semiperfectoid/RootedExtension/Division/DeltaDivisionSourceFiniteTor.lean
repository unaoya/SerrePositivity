module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionSourceGraphKoszul

/-! # 一般除数・任意有限δ座標の源グラフ商のTor

実自由δ射 x_s ↦ d z_s に沿う有限源商のTorを、終域の評価関係の
Koszulホモロジーで計算する。全源評価環への移行は含まない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (c : σ → A)
local notation "P₀" => RelativeFreeDeltaRing (R := A) σ

/-- 指定した有限δ座標の源グラフ関係による実通常商。 -/
abbrev DeltaDivisionSourceFiniteCoordinateQuotient {m : ℕ} (s : Fin m → σ × ℕ) :=
  P₀ ⧸ Ideal.span (Set.range fun i => deltaDivisionSourceGraphRelation D c (s i))

/-- 一般自由δ射に沿う有限源商のTorは、実終域の評価関係Koszulホモロジー。 -/
def deltaDivisionSourceFiniteCoordinateKoszulTorIso {m : ℕ} (s : Fin m → σ × ℕ)
    (hs : Function.Injective s) (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} (deltaDivisionSourceMap (σ := σ) D d)).leftDerived i).obj
      (ModuleCat.of P₀ (DeltaDivisionSourceFiniteCoordinateQuotient D c s)) ≅
      (SerrePositivity.koszulComplex (fun j =>
        deltaDivisionEvaluationRelation D d c (s j).1 (s j).2)).homology (-(i : ℤ)) := by
  have e := SerrePositivity.torAlgKoszulIso (deltaDivisionSourceMap (σ := σ) D d)
    (fun j => deltaDivisionSourceGraphRelation D c (s j))
    (deltaDivisionSourceGraph_fin_isKoszulResolution D c s hs) i
  have he : (deltaDivisionSourceMap (σ := σ) D d) ∘
      (fun j => deltaDivisionSourceGraphRelation D c (s j)) =
      (fun j => deltaDivisionEvaluationRelation D d c (s j).1 (s j).2) := by
    funext j
    exact deltaDivisionSourceGraph_map D d c (s j)
  rw [he] at e
  exact e

/-- 終域の有限評価関係がKoszul分解を与える場合、実有限源商の全正次数Torは零。 -/
theorem deltaDivisionSourceFiniteCoordinate_tor_subsingleton {m : ℕ}
    (s : Fin m → σ × ℕ) (hs : Function.Injective s)
    (hr : SerrePositivity.IsKoszulResolution (fun j =>
      deltaDivisionEvaluationRelation D d c (s j).1 (s j).2)) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg (deltaDivisionSourceMap (σ := σ) D d) (i + 1)
      (DeltaDivisionSourceFiniteCoordinateQuotient D c s)) := by
  have hz := hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)
  have ht := hz.of_iso (deltaDivisionSourceFiniteCoordinateKoszulTorIso D d c s hs (i + 1))
  exact ModuleCat.subsingleton_of_isZero ht

end SerrePositivity.BhattScholze
