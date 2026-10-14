module

public import SerrePositivity.BhattScholze.DeltaDivisionResidueRelation
public import SerrePositivity.BhattScholze.MonicPowerFamilyPresentation

/-! # δ除算包の剰余への最初の通常冪根添加射

係数環のイデアルを消す射を明示して、初期変数のモニック方程式を
通常根添加環からの具体的な射へ接続する。全δ段の表示同型は主張しない。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
  {σ : Type v} {B : Type w} [CommRing B]

/-- δ除算包への係数射と両立する、剰余係数環からの写像。 -/
def deltaDivisionResidueCoefficientMap (D : DeltaStructure p A) (d : A) (a : σ → A)
    (I : Ideal A) (q : DeltaAdjoinDivision D d a →+* B)
    (hI : ∀ r ∈ I, q (deltaAdjoinDivisionMap D d a r) = 0) : A ⧸ I →+* B :=
  Ideal.Quotient.lift I (q.comp (deltaAdjoinDivisionMap D d a)) hI

/-- 初期モニック方程式の剰余係数を、元のδ環の単元から定める。 -/
def deltaDivisionResiduePowerCoefficients (D : DeltaStructure p A) (a : σ → A)
    (I : Ideal A) (u : Aˣ) : σ → A ⧸ I :=
  fun s => Ideal.Quotient.mk I ((u⁻¹ : Aˣ) * D.delta (a s))

/-- 初期変数は剰余係数環上のモニック方程式を満たす。 -/
theorem deltaDivisionResiduePowerRoots (D : DeltaStructure p A) (d : A) (a : σ → A)
    (I : Ideal A) (q : DeltaAdjoinDivision D d a →+* B)
    (hI : ∀ r ∈ I, q (deltaAdjoinDivisionMap D d a r) = 0)
    (hp : q (p : DeltaAdjoinDivision D d a) = 0)
    (hd : q (deltaAdjoinDivisionMap D d a d) = 0)
    (u : Aˣ) (hu : (u : A) = D.delta d) (s : σ) :
    (q (deltaAdjoinDivisionVariable D d a s)) ^ p =
      deltaDivisionResidueCoefficientMap D d a I q hI
        (deltaDivisionResiduePowerCoefficients D a I u s) := by
  let f := q.comp (deltaAdjoinDivisionMap D d a)
  have hunit : ((u.map f : Bˣ) : B) = q (deltaAdjoinDivisionMap D d a (D.delta d)) := by
    change f (u : A) = _
    rw [hu]
    rfl
  have h := deltaAdjoinDivision_variable_pow_residue D d a q hp hd (u.map f) hunit s
  change _ = f ((u⁻¹ : Aˣ) * D.delta (a s))
  rw [map_mul]
  exact h

/-- 剰余係数環上の通常根添加環から、δ除算包の剰余への具体的な射。 -/
def deltaDivisionResiduePowerCoverMap (D : DeltaStructure p A) (d : A) (a : σ → A)
    (I : Ideal A) (q : DeltaAdjoinDivision D d a →+* B)
    (hI : ∀ r ∈ I, q (deltaAdjoinDivisionMap D d a r) = 0)
    (hp : q (p : DeltaAdjoinDivision D d a) = 0)
    (hd : q (deltaAdjoinDivisionMap D d a d) = 0)
    (u : Aˣ) (hu : (u : A) = D.delta d) :
    MonicPowerFamilyCover p σ (A ⧸ I) (deltaDivisionResiduePowerCoefficients D a I u) →+* B :=
  monicPowerFamilyCoverMap p σ (A ⧸ I) _
    (deltaDivisionResidueCoefficientMap D d a I q hI)
    (fun s => q (deltaAdjoinDivisionVariable D d a s))
    (deltaDivisionResiduePowerRoots D d a I q hI hp hd u hu)

/-- 初期根添加射は標準係数射を保つ。 -/
theorem deltaDivisionResiduePowerCoverMap_coeff
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (I : Ideal A) (q : DeltaAdjoinDivision D d a →+* B)
    (hI : ∀ r ∈ I, q (deltaAdjoinDivisionMap D d a r) = 0)
    (hp : q (p : DeltaAdjoinDivision D d a) = 0)
    (hd : q (deltaAdjoinDivisionMap D d a d) = 0)
    (u : Aˣ) (hu : (u : A) = D.delta d) (r : A) :
    deltaDivisionResiduePowerCoverMap D d a I q hI hp hd u hu
      (algebraMap (A ⧸ I) _ (Ideal.Quotient.mk I r)) =
        q (deltaAdjoinDivisionMap D d a r) :=
  RingHom.congr_fun (monicPowerFamilyCoverMap_comp p σ (A ⧸ I) _
    (deltaDivisionResidueCoefficientMap D d a I q hI)
    (fun s => q (deltaAdjoinDivisionVariable D d a s))
    (deltaDivisionResiduePowerRoots D d a I q hI hp hd u hu)) (Ideal.Quotient.mk I r)

/-- 初期根添加射は指定根をδ除算包の初期変数の剰余へ送る。 -/
theorem deltaDivisionResiduePowerCoverMap_root
    (D : DeltaStructure p A) (d : A) (a : σ → A)
    (I : Ideal A) (q : DeltaAdjoinDivision D d a →+* B)
    (hI : ∀ r ∈ I, q (deltaAdjoinDivisionMap D d a r) = 0)
    (hp : q (p : DeltaAdjoinDivision D d a) = 0)
    (hd : q (deltaAdjoinDivisionMap D d a d) = 0)
    (u : Aˣ) (hu : (u : A) = D.delta d) (s : σ) :
    deltaDivisionResiduePowerCoverMap D d a I q hI hp hd u hu
      (monicPowerFamilyRoot p σ (A ⧸ I) (deltaDivisionResiduePowerCoefficients D a I u) s) =
        q (deltaAdjoinDivisionVariable D d a s) :=
  monicPowerFamilyCoverMap_root ..

/-- distinguished dの場合、実際の(p,d)剰余へ初期根添加射が存在する。
この射の全射性や全δ段の表示同型は結論しない。 -/
theorem exists_deltaDivisionFirstPowerCoverToResidue
    (D : DeltaStructure p A) (d : A) (a : σ → A) (hdist : D.IsDistinguished d) :
    let I : Ideal A := Ideal.span {(p : A), d}
    let J : Ideal (DeltaAdjoinDivision D d a) :=
      Ideal.span {(p : DeltaAdjoinDivision D d a), deltaAdjoinDivisionMap D d a d}
    ∃ u : Aˣ, (u : A) = D.delta d ∧
      ∃ L : MonicPowerFamilyCover p σ (A ⧸ I)
        (deltaDivisionResiduePowerCoefficients D a I u) →+* (DeltaAdjoinDivision D d a ⧸ J),
        (∀ r, L (algebraMap (A ⧸ I) _ (Ideal.Quotient.mk I r)) =
          Ideal.Quotient.mk J (deltaAdjoinDivisionMap D d a r)) ∧
        (∀ s, L (monicPowerFamilyRoot p σ (A ⧸ I)
          (deltaDivisionResiduePowerCoefficients D a I u) s) =
          Ideal.Quotient.mk J (deltaAdjoinDivisionVariable D d a s)) := by
  dsimp only
  let I : Ideal A := Ideal.span {(p : A), d}
  let J : Ideal (DeltaAdjoinDivision D d a) :=
    Ideal.span {(p : DeltaAdjoinDivision D d a), deltaAdjoinDivisionMap D d a d}
  let q := Ideal.Quotient.mk J
  have hp : q (p : DeltaAdjoinDivision D d a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hd : q (deltaAdjoinDivisionMap D d a d) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hle : I ≤ RingHom.ker (q.comp (deltaAdjoinDivisionMap D d a)) := by
    apply Ideal.span_le.mpr
    intro r hr
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · change q (deltaAdjoinDivisionMap D d a (p : A)) = 0
      simpa only [map_natCast] using hp
    · exact hd
  have hI : ∀ r ∈ I, q (deltaAdjoinDivisionMap D d a r) = 0 := fun r hr => hle hr
  obtain ⟨u, hu⟩ := hdist
  exact ⟨u, hu, deltaDivisionResiduePowerCoverMap D d a I q hI hp hd u hu,
    deltaDivisionResiduePowerCoverMap_coeff D d a I q hI hp hd u hu,
    deltaDivisionResiduePowerCoverMap_root D d a I q hI hp hd u hu⟩

end SerrePositivity.BhattScholze
