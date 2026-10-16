module

public import SerrePositivity.BhattScholze.RelativeDeltaEstimate

/-! # δ写像のイデアル冪に対する評価

BS著者公開版Lemma 2.17の連続性に使う代数的評価。
p∈Iならδ(I^{n+1})⊂I^nを証明する。有限生成性・p正則性・完備性は不要。
完備化へのδ構造の延長はここでは構成しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

namespace DeltaStructure

/-- pを含むイデアルのn+1乗の元のδは、そのn乗に属する。 -/
theorem delta_mem_pow (D : DeltaStructure p R) (I : Ideal R) (hp : (p : R) ∈ I)
    (n : ℕ) (x : R) (hx : x ∈ I ^ (n + 1)) : D.delta x ∈ I ^ n := by
  exact wittTwoLift_delta_mem_pow (RingHom.id R) D.sectionHom D.projection_comp I hp n x
    (by simpa only [Ideal.comap_id] using hx)

/-- I^{n+1}の摂動でδの値はI^nの範囲でしか変わらない。
Lemma 2.17の具体的な連続性評価m=n+1。 -/
theorem delta_add_sub_mem_pow (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (n : ℕ) (x y : R) (hy : y ∈ I ^ (n + 1)) :
    D.delta (x + y) - D.delta x ∈ I ^ n := by
  exact wittTwoLift_delta_add_sub_mem_pow (RingHom.id R) D.sectionHom D.projection_comp I hp n x y
    (by simpa only [Ideal.comap_id] using hy)

/-- x,yがmod I^{n+1}で一致すればδx,δyはmod I^nで一致する。 -/
theorem delta_sub_mem_pow (D : DeltaStructure p R) (I : Ideal R)
    (hp : (p : R) ∈ I) (n : ℕ) (x y : R) (hxy : x - y ∈ I ^ (n + 1)) :
    D.delta x - D.delta y ∈ I ^ n := by
  exact wittTwoLift_delta_sub_mem_pow (RingHom.id R) D.sectionHom D.projection_comp I hp n x y
    (by simpa only [Ideal.comap_id] using hxy)

end DeltaStructure
end SerrePositivity.BhattScholze
