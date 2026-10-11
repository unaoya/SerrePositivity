module

public import SerrePositivity.HomologicalAlgebra.KoszulRestriction
public import SerrePositivity.PerfectComplex.SupProperty

/-! # 部分代数の増大列と Koszul ホモロジー

基底環 `R` 上の部分代数 `Bₙ ⊆ C` が増大して `C` を覆うとき、`B₀` の元の列の
Koszul ホモロジーを全段で同じ `R` 加群圏に置く。ホモロジーと有向極限の同型、
および正規化長さの零への収束から極限の長さの消滅を導く。
近似環そのものの平坦性やホモロジーの遷移写像の単射性は要求しない。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false

variable (R C : Type u) [CommRing R] [CommRing C] [Algebra R C]
    (B : ℕ → Subalgebra R C) (hB : Monotone B)

/-- 初段から各部分代数への包含。列の元を全段で共通に扱うための底環写像。 -/
def subalgebraStageBaseMap (n : ℕ) : B 0 →+* B n :=
  (Subalgebra.inclusion (hB (Nat.zero_le n))).toRingHom

/-- 段への包含は、全体の環で見れば元を変えない。 -/
@[simp] theorem subalgebraStageBaseMap_coe (n : ℕ) (x : B 0) :
    (subalgebraStageBaseMap R C B hB n x : C) = (x : C) := rfl

/-- 部分代数の増大列を初段上の加群の図式として表す。 -/
noncomputable def subalgebraModuleDiagram : ℕ ⥤ ModuleCat.{u} (B 0) where
  obj n := (ModuleCat.restrictScalars (subalgebraStageBaseMap R C B hB n)).obj
    (ModuleCat.of (B n) (B n))
  map {n m} f := by
    letI := Module.compHom (B n) (subalgebraStageBaseMap R C B hB n)
    letI := Module.compHom (B m) (subalgebraStageBaseMap R C B hB m)
    exact ModuleCat.ofHom
      { toFun := Subalgebra.inclusion (hB f.le)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- 各部分代数の包含からなる余錐。頂点は `C` を初段の加群とみたもの。 -/
noncomputable def subalgebraModuleCocone : Cocone (subalgebraModuleDiagram R C B hB) where
  pt := (ModuleCat.restrictScalars (B 0).val.toRingHom).obj (ModuleCat.of C C)
  ι :=
    { app n := by
        letI := Module.compHom (B n) (subalgebraStageBaseMap R C B hB n)
        letI := Module.compHom C (B 0).val.toRingHom
        exact ModuleCat.ofHom
          { toFun := (B n).val
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
      naturality _ _ _ := by ext; rfl }

variable {r : ℕ} (z : Fin r → B 0)

/-- 各部分代数の Koszul 複体を共通の `R` 加群圏で表す図式。 -/
noncomputable def subalgebraKoszulDiagram : ℕ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  subalgebraModuleDiagram R C B hB ⋙ koszulModuleFunctor z ⋙
    (ModuleCat.restrictScalars (algebraMap R (B 0))).mapHomologicalComplex (.up ℤ)

/-- 共通の係数圏に置いた Koszul 複体の余錐。 -/
noncomputable def subalgebraKoszulCocone : Cocone (subalgebraKoszulDiagram R C B hB z) :=
  ((koszulModuleFunctor z) ⋙
    (ModuleCat.restrictScalars (algebraMap R (B 0))).mapHomologicalComplex (.up ℤ)).mapCocone
      (subalgebraModuleCocone R C B hB)

/-- 共通の係数圏で作った各段のホモロジーは、部分代数上の Koszul ホモロジーである。 -/
noncomputable def subalgebraKoszulStageHomologyIso (n : ℕ) (i : ℤ) :
    ((subalgebraKoszulDiagram R C B hB z).obj n).homology i ≅
      (ModuleCat.restrictScalars (algebraMap R (B n))).obj
        ((koszulComplex (subalgebraStageBaseMap R C B hB n ∘ z)).homology i) := by
  have he : (subalgebraStageBaseMap R C B hB n).comp (algebraMap R (B 0)) =
      algebraMap R (B n) := by ext; rfl
  have e := koszulModuleRestrictedHomologyIso
    (subalgebraStageBaseMap R C B hB n) (algebraMap R (B 0)) z i
  rw [he] at e
  exact e

/-- 余錐の頂点のホモロジーは、`C` 上の Koszul ホモロジーの係数制限である。 -/
noncomputable def subalgebraKoszulTargetHomologyIso (i : ℤ) :
    (subalgebraKoszulCocone R C B hB z).pt.homology i ≅
      (ModuleCat.restrictScalars (algebraMap R C)).obj
        ((koszulComplex ((B 0).val ∘ z)).homology i) := by
  have he : (B 0).val.toRingHom.comp (algebraMap R (B 0)) = algebraMap R C := by ext; rfl
  have e := koszulModuleRestrictedHomologyIso (B 0).val.toRingHom (algebraMap R (B 0)) z i
  rw [he] at e
  exact e

/-- 部分代数の包含は、共通の係数圏の Koszul 複体でも各次数で単射。 -/
theorem subalgebraKoszul_cocone_injective (n : ℕ) (i : ℤ) :
    Function.Injective (((subalgebraKoszulCocone R C B hB z).ι.app n).f i) := by
  exact koszulModule_cocone_injective (subalgebraModuleDiagram R C B hB)
    (subalgebraModuleCocone R C B hB) z (fun _ ↦ Subtype.val_injective) n i

variable (hcover : ∀ x : C, ∃ n, x ∈ B n)

include hcover in
/-- 部分代数が全体を覆えば、共通の係数圏の Koszul 複体も各次数で全体を覆う。 -/
theorem subalgebraKoszul_cocone_cover (i : ℤ)
    (x : (subalgebraKoszulCocone R C B hB z).pt.X i) :
    ∃ n y, ((subalgebraKoszulCocone R C B hB z).ι.app n).f i y = x := by
  exact koszulModule_cocone_cover (subalgebraModuleDiagram R C B hB)
    (subalgebraModuleCocone R C B hB) z (fun x ↦ by
      obtain ⟨n, hn⟩ := hcover x
      exact ⟨n, ⟨x, hn⟩, rfl⟩) i x

include hcover in
/-- 部分代数の増大列について、Koszul ホモロジーと有向極限が可換となる `R` 線形同型。 -/
noncomputable def subalgebraKoszulHomologyDirectLimitEquiv (i : ℤ) :
    Module.DirectLimit
      (fun n ↦ ((subalgebraKoszulDiagram R C B hB z).obj n).homology i)
      (homologyStageMap (subalgebraKoszulDiagram R C B hB z) i) ≃ₗ[R]
        (ModuleCat.restrictScalars (algebraMap R C)).obj
          ((koszulComplex ((B 0).val ∘ z)).homology i) :=
  (homologyDirectLimitEquiv _ _ (subalgebraKoszul_cocone_injective R C B hB z)
    (subalgebraKoszul_cocone_cover R C B hB z hcover) i).trans
      (subalgebraKoszulTargetHomologyIso R C B hB z i).toLinearEquiv

include hcover in
/-- 全段に共通の消去冪があり、各段の Koszul ホモロジーの正規化長さが零へ収束すれば、
全体の Koszul ホモロジーの長さは零になる。 -/
theorem subalgebraKoszulHomology_len_eq_zero {J : Ideal R}
    (lam : NormalizedLength R J) (hsup : lam.HasSup) (i : ℤ)
    (N : ℕ)
    (hN : ∀ n, Module.IsTorsionBySet R
      ((ModuleCat.restrictScalars (algebraMap R (B n))).obj
        ((koszulComplex (subalgebraStageBaseMap R C B hB n ∘ z)).homology i))
      (J ^ N : Ideal R))
    (hlim : Filter.Tendsto (fun n ↦ lam.len
      ((ModuleCat.restrictScalars (algebraMap R (B n))).obj
        ((koszulComplex (subalgebraStageBaseMap R C B hB n ∘ z)).homology i)))
      Filter.atTop (nhds 0)) :
    lam.len ((ModuleCat.restrictScalars (algebraMap R C)).obj
      ((koszulComplex ((B 0).val ∘ z)).homology i)) = 0 := by
  let F := subalgebraKoszulDiagram R C B hB z
  let c := subalgebraKoszulCocone R C B hB z
  let g (n : ℕ) : (F.obj n).homology i →ₗ[R] c.pt.homology i :=
    (homologyMap (c.ι.app n) i).hom
  have hmono : Monotone (fun n ↦ LinearMap.range (g n)) := by
    rintro n m hnm _ ⟨x, rfl⟩
    refine ⟨homologyMap (F.map (homOfLE hnm)) i x, ?_⟩
    have he := congrArg (fun f : F.obj n ⟶ c.pt ↦ (homologyMap f i).hom x)
      (c.w (homOfLE hnm))
    rw [homologyMap_comp] at he
    exact he
  have hcover' := homology_exists_stage F c
    (subalgebraKoszul_cocone_injective R C B hB z)
    (subalgebraKoszul_cocone_cover R C B hB z hcover) i
  have ht n : Module.IsTorsionBySet R ((F.obj n).homology i) (J ^ N : Ideal R) := by
    intro x a
    let e := (subalgebraKoszulStageHomologyIso R C B hB z n i).toLinearEquiv
    apply e.injective
    rw [e.map_smul, hN n (x := e x) (a := a), map_zero]
  have he n := lam.len_congr _ _
    (subalgebraKoszulStageHomologyIso R C B hB z n i).toLinearEquiv
  have hl : Filter.Tendsto (fun n ↦ lam.len ((F.obj n).homology i))
      Filter.atTop (nhds 0) := by
    simpa only [F, he] using hlim
  have hzero := NormalizedLength.len_eq_zero_of_directed_cover hsup
    (fun n ↦ (F.obj n).homology i) g hmono hcover' N ht hl
  rw [lam.len_congr _ _ (subalgebraKoszulTargetHomologyIso R C B hB z i).toLinearEquiv]
    at hzero
  exact hzero

end SerrePositivity
