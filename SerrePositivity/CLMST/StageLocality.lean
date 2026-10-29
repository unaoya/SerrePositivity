module

public import SerrePositivity.CLMST.StageBaseChange
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Finite
public import SerrePositivity.CLMST.StageDimension

/-! # CLMST の一般段の局所性

有限段のテンソル積を D 上の根の塔の表示へ移し、既存の局所性の定理を適用する。
必要なのは D の局所性、素数 p、座標の像が極大イデアルに属することである。
Noether 性・完備性・整域性・perfectoid 化の引用は使わない。
パラメータ系である場合は、その根基の条件から所属を供給する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open Section2 IsLocalRing

variable (A D : Type u) [CommRing A] [CommRing D] [Algebra A D]
    [IsLocalRing D] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- 座標の D での像が極大イデアルに入れば、すべての有限段は局所環。 -/
theorem stageAlgebra_isLocalRing (htD : ∀ i, algebraMap A D (t i) ∈ maximalIdeal D)
    (n : ℕ) : IsLocalRing (StageAlgebra A D t p n) := by
  let : IsLocalRing (TowerStage D (algebraMap A D ∘ t) p n) :=
    isLocalRing_towerStage D (algebraMap A D ∘ t) p htD n
  let e := stageBaseChangeEquiv A D t p n
  have : Nontrivial (StageAlgebra A D t p n) :=
    ⟨⟨e.symm 0, e.symm 1, fun h ↦ zero_ne_one (e.symm.injective h)⟩⟩
  exact IsLocalRing.of_surjective' e.symm.toRingHom e.symm.surjective

/-- D のパラメータ系を含む標準基底から、一般段の局所環構造を供給する。
局所性そのものを外部の仮定として受け取る必要はない。 -/
theorem stageAlgebra_isLocalRing_of_parameters
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t)) (n : ℕ) :
    IsLocalRing (StageAlgebra A D t p n) := by
  apply stageAlgebra_isLocalRing A D t p _ n
  intro i
  rw [← hsop.2]
  exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self i))

/-- D のパラメータ系は、すべての有限段に標準写像で移せる。
局所性と有限単射性を、いずれも構成から証明して使う。 -/
theorem isSystemOfParameters_stageAlgebra
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t)) (n : ℕ)
    {r : ℕ} (z : Fin r → D) (hz : IsSystemOfParameters D z) :
    let _ := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
    IsSystemOfParameters (StageAlgebra A D t p n)
      (algebraMap D (StageAlgebra A D t p n) ∘ z) := by
  let := stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  exact hz.map_finite (StageAlgebra A D t p n)
    (stageAlgebra_algebraMap_injective A D t p n)

end SerrePositivity.CLMST
