module

public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution

/-! # 第零ホモロジーからの具体的な全射

微分を消す零次項の全射は第零ホモロジーを経由する。さらに、行き先を消す
スカラーで Koszul 反復を行っても全射は保たれる。長さ・平坦性・射影性は不要。
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R]

/-- 出る微分が零なら、入る微分を消す射は第零ホモロジーから降りる。 -/
noncomputable def homologyZeroDesc
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.d 0 1 = 0)
    {Y : ModuleCat.{u} R} (f : P.X 0 ⟶ Y) (hf : P.d (-1) 0 ≫ f = 0) :
    P.homology 0 ⟶ Y :=
  (P.isoHomologyι 0 1 (by simp) hP).hom ≫ P.descOpcycles f (-1) (by simp) hf

/-- 零次項からの全射はホモロジーからも全射を与える。 -/
instance homologyZeroDesc_epi
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.d 0 1 = 0)
    {Y : ModuleCat.{u} R} (f : P.X 0 ⟶ Y) (hf : P.d (-1) 0 ≫ f = 0) [Epi f] :
    Epi (homologyZeroDesc P hP f hf) := by
  have : Epi (P.descOpcycles f (-1) (by simp) hf) :=
    epi_of_epi_fac (P.p_descOpcycles f (-1) (by simp) hf)
  dsimp [homologyZeroDesc]
  infer_instance

/-- 非正次数のホモロジーをもつ複体に Koszul 反復を施しても、正次数は零。 -/
lemma koszulComplexOn_homology_isZero_of_pos
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ q : ℤ, 0 < q → IsZero (P.homology q)) {n : ℕ} (x : Fin n → R)
    (q : ℤ) (hq : 0 < q) : IsZero ((koszulComplexOn x P).homology q) := by
  induction n generalizing q with
  | zero => exact hP q hq
  | succ n ih =>
    exact (Cone.exact₃ (smulId (x (Fin.last n)) (koszulComplexOn (Fin.init x) P))
      q (q + 1) rfl).isZero_X₂ ((ih (Fin.init x) q hq).eq_zero_of_src _)
        ((ih (Fin.init x) (q + 1) (by omega)).eq_zero_of_tgt _)

/-- スカラーが行き先を消すなら、Koszul 第零ホモロジーからも同じ行き先へ全射がある。
元の複体でスカラーが零ホモトピックである必要はない。 -/
theorem exists_koszul_homologyZero_epi
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ q : ℤ, 0 < q → IsZero (P.homology q))
    {Y : ModuleCat.{u} R} (f : P.homology 0 ⟶ Y) [hfepi : Epi f]
    {n : ℕ} (x : Fin n → R) (hx : ∀ j, x j • 𝟙 Y = 0) :
    ∃ g : (koszulComplexOn x P).homology 0 ⟶ Y, Epi g := by
  induction n with
  | zero => exact ⟨f, hfepi⟩
  | succ n ih =>
    obtain ⟨g, hg⟩ := ih (Fin.init x) (fun j ↦ hx j.castSucc)
    let Q := koszulComplexOn (Fin.init x) P
    let a := x (Fin.last n)
    have hepi : Epi (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (smulId a Q)) 0) :=
      (Cone.exact₃ (smulId a Q) 0 1 rfl).epi_f
        ((koszulComplexOn_homology_isZero_of_pos P hP (Fin.init x) 1 one_pos).eq_zero_of_tgt _)
    have hcomp : HomologicalComplex.homologyMap (smulId a Q) 0 ≫ g = 0 := by
      rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id,
        Linear.smul_comp, Category.id_comp]
      have h := congrArg (fun k : Y ⟶ Y ↦ g ≫ k) (hx (Fin.last n))
      simpa only [Linear.comp_smul, Category.comp_id, comp_zero] using h
    let h := Cone.exact₂ (smulId a Q) 0
    exact ⟨h.desc g hcomp, epi_of_epi_fac (h.g_desc g hcomp)⟩

/-- 座標ごとの商写像。 -/
def coordinateQuotient (I : Ideal R) (b : ℕ) :
    ModuleCat.of R (Fin b → R) ⟶ ModuleCat.of R (Fin b → R ⧸ I) :=
  ModuleCat.ofHom (LinearMap.pi (fun j ↦ I.mkQ.comp (LinearMap.proj j)))

instance coordinateQuotient_epi (I : Ideal R) (b : ℕ) : Epi (coordinateQuotient I b) := by
  classical
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro y
  choose x hx using fun j ↦ I.mkQ_surjective (y j)
  exact ⟨x, funext hx⟩

/-- 微分の座標が `I` に入ることから、`H⁰(P) → (R/I)^b` を構成する。 -/
noncomputable def minimalHomologyZeroQuotient
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.d 0 1 = 0)
    (I : Ideal R) (b : ℕ) (e : P.X 0 ≅ ModuleCat.of R (Fin b → R))
    (hmin : ∀ m : P.X (-1), ∀ j, e.hom.hom ((P.d (-1) 0).hom m) j ∈ I) :
    P.homology 0 ⟶ ModuleCat.of R (Fin b → R ⧸ I) :=
  homologyZeroDesc P hP (e.hom ≫ coordinateQuotient I b) (by
    ext m j
    exact (Submodule.Quotient.mk_eq_zero _).mpr (hmin m j))

instance minimalHomologyZeroQuotient_epi
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : P.d 0 1 = 0)
    (I : Ideal R) (b : ℕ) (e : P.X 0 ≅ ModuleCat.of R (Fin b → R))
    (hmin : ∀ m : P.X (-1), ∀ j, e.hom.hom ((P.d (-1) 0).hom m) j ∈ I) :
    Epi (minimalHomologyZeroQuotient P hP I b e hmin) := by
  dsimp [minimalHomologyZeroQuotient]
  infer_instance

/-- 極小性と `x_j ∈ I` から、実際の Koszul 第零ホモロジーの全射を得る。 -/
theorem exists_minimal_koszul_homologyZero_epi
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : ∀ q : ℤ, 0 < q → IsZero (P.X q))
    (I : Ideal R) (b : ℕ) (e : P.X 0 ≅ ModuleCat.of R (Fin b → R))
    (hmin : ∀ m : P.X (-1), ∀ j, e.hom.hom ((P.d (-1) 0).hom m) j ∈ I)
    {n : ℕ} (x : Fin n → R) (hx : ∀ j, x j ∈ I) :
    ∃ g : (koszulComplexOn x P).homology 0 ⟶ ModuleCat.of R (Fin b → R ⧸ I), Epi g := by
  apply exists_koszul_homologyZero_epi P
    (fun q hq ↦ (P.sc q).isZero_homology_of_isZero_X₂ (hP q hq))
    (minimalHomologyZeroQuotient P ((hP 1 one_pos).eq_zero_of_tgt _) I b e hmin) x
  intro j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  funext k
  change x j • y k = 0
  obtain ⟨r, hr⟩ := I.mkQ_surjective (y k)
  rw [← hr, ← map_smul]
  exact (Submodule.Quotient.mk_eq_zero I).mpr
    (by simpa [smul_eq_mul, mul_comm] using I.mul_mem_right r (hx j))

end SerrePositivity
