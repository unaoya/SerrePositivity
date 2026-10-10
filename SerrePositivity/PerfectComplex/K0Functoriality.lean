module

public import SerrePositivity.PerfectComplex.BaseChange
public import SerrePositivity.PerfectComplex.K0Comparison
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence

/-! # 有限射影 K₀ の係数変更・群作用と有限自由モデルとの両立

支持パラメータを固定して係数変更を合成する。
環の群作用から得られる有限射影 K₀ の作用は、旧有限自由 K₀ の作用と一致する。
環の局所性は使わない。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Functor

variable {R S V : Type u} [CommRing R] [CommRing S] [CommRing V] {e : ℕ}

/-- 恒等環準同型による有限射影圏の係数変更は恒等関手と自然同型。 -/
noncomputable def perfectChangeRingIdIso :
    perfectChangeRing (RingHom.id R) ≅ 𝟭 (PerfectHomotopy R) := by
  let i : (ModuleCat.extendScalars (RingHom.id R)).mapHomotopyCategory (.up ℤ) ≅
      𝟭 (HomotopyCategory (ModuleCat.{u} R) (.up ℤ)) :=
    NatIso.mapHomotopyCategory (ModuleCat.extendScalarsId R) (.up ℤ) ≪≫
      Quotient.natIsoLift _ (isoWhiskerRight
        (Functor.mapHomologicalComplexIdIso (ModuleCat.{u} R) (.up ℤ))
        (HomotopyCategory.quotient _ _))
  exact NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (i.app X.obj)) (fun f ↦ by
    apply ObjectProperty.hom_ext
    exact i.hom.naturality f.hom)

/-- 恒等係数変更の自然同型を支持部分圏に制限する。 -/
noncomputable def supportedPerfectChangeRingIdIso (z : Fin e → R) :
    supportedPerfectChangeRing (RingHom.id R) z ≅ 𝟭 (SupportedPerfectHomotopy z) :=
  NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (perfectChangeRingIdIso.app X.obj))
    (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact perfectChangeRingIdIso.hom.naturality f.hom)

/-- 有限自由／有限射影 K₀ の比較写像は任意の係数変更と可換。 -/
lemma freeToPerfectK0_changeRing (φ : R →+* S) (z : Fin e → R) :
    (TriangulatedK0.map (supportedPerfectChangeRing φ z)).comp freeToPerfectK0 =
      freeToPerfectK0.comp (K0.map φ) := by
  apply K0.hom_ext
  intro P
  simp only [AddMonoidHom.comp_apply, freeToPerfectK0_mk, TriangulatedK0.map_mk, K0.map_mk]
  rfl

/-- 変更先の支持パラメータを指定した係数変更。 -/
noncomputable def supportedPerfectChangeRingTo (φ : R →+* S)
    (z : Fin e → R) (w : Fin e → S) (h : φ ∘ z = w) :
    SupportedPerfectHomotopy z ⥤ SupportedPerfectHomotopy w := by
  subst w
  exact supportedPerfectChangeRing φ z

noncomputable instance (φ : R →+* S) (z : Fin e → R) (w : Fin e → S) (h : φ ∘ z = w) :
    (supportedPerfectChangeRingTo φ z w h).CommShift ℤ := by
  subst w
  dsimp [supportedPerfectChangeRingTo]
  infer_instance

instance (φ : R →+* S) (z : Fin e → R) (w : Fin e → S) (h : φ ∘ z = w) :
    (supportedPerfectChangeRingTo φ z w h).IsTriangulated := by
  subst w
  dsimp [supportedPerfectChangeRingTo]
  infer_instance

/-- パラメータを指定した係数変更の K₀ 写像。 -/
noncomputable def supportedPerfectMap (φ : R →+* S)
    (z : Fin e → R) (w : Fin e → S) (h : φ ∘ z = w) :
    TriangulatedK0 (SupportedPerfectHomotopy z) →+
      TriangulatedK0 (SupportedPerfectHomotopy w) :=
  TriangulatedK0.map (supportedPerfectChangeRingTo φ z w h)

/-- 同じ環準同型による K₀ 写像はパラメータの等式の証明によらない。 -/
lemma supportedPerfectMap_congr (φ ψ : R →+* S) (z : Fin e → R) (w : Fin e → S)
    (h : φ ∘ z = w) (k : ψ ∘ z = w) (hφ : φ = ψ) :
    supportedPerfectMap φ z w h = supportedPerfectMap ψ z w k := by
  subst ψ
  rfl

/-- 係数変更の合成則は、固定した支持パラメータの K₀ 上でも成立する。 -/
lemma supportedPerfectMap_comp (φ : R →+* S) (ψ : S →+* V)
    (z : Fin e → R) (w : Fin e → S) (v : Fin e → V)
    (h : φ ∘ z = w) (k : ψ ∘ w = v) :
    (supportedPerfectMap ψ w v k).comp (supportedPerfectMap φ z w h) =
      supportedPerfectMap (ψ.comp φ) z v (by rw [← k, ← h]; rfl) := by
  subst w v
  change (TriangulatedK0.map (supportedPerfectChangeRing ψ (φ ∘ z))).comp
    (TriangulatedK0.map (supportedPerfectChangeRing φ z)) = _
  rw [← TriangulatedK0.map_comp]
  exact TriangulatedK0.map_natIso _ (supportedPerfectChangeRingCompIso φ z ψ)

/-- 恒等係数変更は K₀ の恒等写像を与える。 -/
lemma supportedPerfectMap_id (z : Fin e → R) :
    supportedPerfectMap (RingHom.id R) z z rfl = AddMonoidHom.id _ := by
  change TriangulatedK0.map (supportedPerfectChangeRing (RingHom.id R) z) = _
  rw [TriangulatedK0.map_natIso _ (supportedPerfectChangeRingIdIso z), TriangulatedK0.map_id]

/-- 有限自由代表上の係数変更の計算式。 -/
lemma supportedPerfectMap_mk (φ : R →+* S) (z : Fin e → R) (w : Fin e → S)
    (h : φ ∘ z = w) (P : PerfSupp R z) :
    supportedPerfectMap φ z w h (TriangulatedK0.mk (perfSuppHomotopyObj P)) =
      TriangulatedK0.mk (perfSuppHomotopyObj
        ⟨baseChange φ P.1, by rw [← h]; exact isPerfectSupported_baseChange φ P.2⟩) := by
  subst w
  rw [supportedPerfectMap, TriangulatedK0.map_mk]
  rfl

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]
  (z : Fin e → A) {G : Type u} [Group G] [MulSemiringAction G T] [SMulCommClass G A T]

/-- A 上の作用は支持パラメータを固定する。 -/
lemma perfectTwist_parameters (g : G) :
    (MulSemiringAction.toAlgHom A T g).toRingHom ∘ (algebraMap A T ∘ z) =
      algebraMap A T ∘ z := by
  funext j
  exact (MulSemiringAction.toAlgHom A T g).commutes (z j)

/-- 有限射影支持圏の実際のひねり関手。係数拡大なので群の積に関して共変。 -/
noncomputable abbrev perfectTwist (g : G) :
    SupportedPerfectHomotopy (algebraMap A T ∘ z) ⥤
      SupportedPerfectHomotopy (algebraMap A T ∘ z) :=
  supportedPerfectChangeRingTo (MulSemiringAction.toAlgHom A T g).toRingHom
    (algebraMap A T ∘ z) (algebraMap A T ∘ z) (perfectTwist_parameters z g)

noncomputable abbrev perfectTwistK0 (g : G) :
    TriangulatedK0 (SupportedPerfectHomotopy (algebraMap A T ∘ z)) →+
      TriangulatedK0 (SupportedPerfectHomotopy (algebraMap A T ∘ z)) :=
  TriangulatedK0.map (perfectTwist (T := T) z g)

lemma perfectTwistK0_one :
    perfectTwistK0 (T := T) z (1 : G) = AddMonoidHom.id _ := by
  have h : (MulSemiringAction.toAlgHom A T (1 : G)).toRingHom = RingHom.id T := by
    ext x
    simp
  change supportedPerfectMap _ _ _ _ = _
  simp only [h]
  exact supportedPerfectMap_id _

lemma perfectTwistK0_mul (g h : G) :
    perfectTwistK0 (T := T) z (g * h) =
      (perfectTwistK0 (T := T) z g).comp (perfectTwistK0 (T := T) z h) := by
  have hh : (MulSemiringAction.toAlgHom A T (g * h)).toRingHom =
      (MulSemiringAction.toAlgHom A T g).toRingHom.comp
        (MulSemiringAction.toAlgHom A T h).toRingHom := by
    ext x
    exact mul_smul g h x
  have hc := supportedPerfectMap_comp
    (MulSemiringAction.toAlgHom A T h).toRingHom
    (MulSemiringAction.toAlgHom A T g).toRingHom
    (algebraMap A T ∘ z) (algebraMap A T ∘ z) (algebraMap A T ∘ z)
    (perfectTwist_parameters z h) (perfectTwist_parameters z g)
  change supportedPerfectMap (MulSemiringAction.toAlgHom A T (g * h)).toRingHom
    (algebraMap A T ∘ z) (algebraMap A T ∘ z) _ = _
  exact (supportedPerfectMap_congr _ _ _ _ _ _ hh).trans hc.symm

/-- 有限射影 K₀ 上の、環の群作用から誘導される加法的な左作用。 -/
noncomputable instance perfectK0DistribMulAction :
    DistribMulAction G (TriangulatedK0 (SupportedPerfectHomotopy (algebraMap A T ∘ z))) where
  smul g := perfectTwistK0 (T := T) z g
  one_smul x := DFunLike.congr_fun (perfectTwistK0_one (T := T) (G := G) z) x
  mul_smul g h x := DFunLike.congr_fun (perfectTwistK0_mul (T := T) z g h) x
  smul_zero g := (perfectTwistK0 (T := T) z g).map_zero
  smul_add g x y := (perfectTwistK0 (T := T) z g).map_add x y

/-- 対象の類への群作用は、実際のひねり関手による像の類である。 -/
lemma perfectK0_smul_mk (g : G)
    (X : SupportedPerfectHomotopy (algebraMap A T ∘ z)) :
    g • TriangulatedK0.mk X = TriangulatedK0.mk ((perfectTwist (T := T) z g).obj X) :=
  TriangulatedK0.map_mk _ _

/-- 群の元による係数拡大は、逆元に沿う旧係数制限のひねりと同型。 -/
noncomputable def baseChange_smul_iso_twist (g : G)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    baseChange (MulSemiringAction.toRingHom G T g) P ≅ twist g⁻¹ P := by
  let σ := MulSemiringAction.toRingEquiv G T g⁻¹
  have hσ : σ.symm.toRingHom = MulSemiringAction.toRingHom G T g := by
    ext t
    change (g⁻¹)⁻¹ • t = g • t
    rw [inv_inv]
  let i := ((NatIso.mapHomologicalComplex
    (restrictScalarsIsoExtendInverse σ) (.up ℤ)).app P).symm
  change baseChange σ.symm.toRingHom P ≅ twist g⁻¹ P at i
  rw [hσ] at i
  exact i

/-- K₀ 比較写像は、新しい共変ひねりと旧来の逆元による反変ひねりを結ぶ。 -/
lemma perfectTwistK0_comp_freeToPerfectK0 (g : G) :
    (perfectTwistK0 (T := T) z g).comp freeToPerfectK0 =
      freeToPerfectK0.comp (K0.twistHom (A := A) (T := T) (z := z) g⁻¹) := by
  apply K0.hom_ext
  intro P
  simp only [AddMonoidHom.comp_apply, freeToPerfectK0_mk, K0.twistHom_mk]
  change supportedPerfectMap _ _ _ _ _ = _
  rw [supportedPerfectMap_mk]
  exact TriangulatedK0.mk_iso (perfSuppHomotopyIso _ _
    (HomotopyEquiv.ofIso (baseChange_smul_iso_twist g P.1)))

/-- 任意の可換環上で、有限自由から有限射影への K₀ 比較は同変である。 -/
lemma freeToPerfectK0_smul (g : G) (x : K0Supported T (algebraMap A T ∘ z)) :
    freeToPerfectK0 (g • x) = g • freeToPerfectK0 x :=
  (DFunLike.congr_fun (perfectTwistK0_comp_freeToPerfectK0 z g) x).symm

variable [IsLocalRing T]

/-- 局所環上では比較同型の逆も同変であり、旧作用と新作用は同じ群作用になる。 -/
lemma perfectToFreeK0_smul (g : G)
    (x : TriangulatedK0 (SupportedPerfectHomotopy (algebraMap A T ∘ z))) :
    perfectToFreeK0 (g • x) = g • perfectToFreeK0 x := by
  apply (freePerfectK0Equiv (z := algebraMap A T ∘ z)).injective
  change freeToPerfectK0 (perfectToFreeK0 (g • x)) =
    freeToPerfectK0 (g • perfectToFreeK0 x)
  rw [freeToPerfectK0_smul]
  have hi (y : TriangulatedK0 (SupportedPerfectHomotopy (algebraMap A T ∘ z))) :
      freeToPerfectK0 (perfectToFreeK0 y) = y :=
    DFunLike.congr_fun freeToPerfectK0_comp_perfectToFreeK0 y
  rw [hi, hi]

/-- 局所的な係数環では、旧有限自由 K₀ の不変類の降下を有限射影版へ移せる。
降下そのものの証明を入力とし、新たな降下の公理は要求しない。 -/
theorem perfectK0_descent_of_free
    (hdesc : ∀ y : K0Supported T (algebraMap A T ∘ z), (∀ g : G, g • y = y) →
      ∃ (n : ℕ) (x : K0Supported A z), 0 < n ∧ n • y = K0.map (algebraMap A T) x)
    (y : TriangulatedK0 (SupportedPerfectHomotopy (algebraMap A T ∘ z)))
    (hy : ∀ g : G, g • y = y) :
    ∃ (n : ℕ) (x : TriangulatedK0 (SupportedPerfectHomotopy z)), 0 < n ∧
      n • y = TriangulatedK0.map (supportedPerfectChangeRing (algebraMap A T) z) x := by
  obtain ⟨n, x, hn, hx⟩ := hdesc (perfectToFreeK0 y) (fun g ↦ by
    rw [← perfectToFreeK0_smul, hy g])
  refine ⟨n, freeToPerfectK0 x, hn, ?_⟩
  have h := congrArg (freeToPerfectK0 (z := algebraMap A T ∘ z)) hx
  rw [_root_.map_nsmul] at h
  have hi : freeToPerfectK0 (perfectToFreeK0 y) = y :=
    DFunLike.congr_fun freeToPerfectK0_comp_perfectToFreeK0 y
  rw [hi] at h
  exact h.trans (DFunLike.congr_fun (freeToPerfectK0_changeRing (algebraMap A T) z) x).symm

end SerrePositivity
