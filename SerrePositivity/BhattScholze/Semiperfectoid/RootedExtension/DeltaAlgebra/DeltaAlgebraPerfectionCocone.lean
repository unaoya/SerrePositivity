module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaAlgebra.DeltaAlgebraFrobeniusStages
public import SerrePositivity.BhattScholze.Delta.Perfect.DeltaPerfection
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # 実Frobenius環段から既存δ完全化への正確なA線形余錐 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (D : DeltaStructure p A) (E : DeltaStructure p B) (j : A →+* B)

/-- 実δ完全化の元のA係数射は、既存の第0段標準射を通る。 -/
def deltaAlgebraPerfectionCoefficient : A →+* DeltaPerfection E :=
  (deltaPerfectionOf E 0).comp j

/-- 元の係数射がδ射なら、実δ完全化の同じ係数射もδ射。 -/
theorem deltaAlgebraPerfectionCoefficient_isDeltaHom (hj : D.IsDeltaHom E j) :
    D.IsDeltaHom (deltaPerfectionStructure E) (deltaAlgebraPerfectionCoefficient E j) :=
  (deltaPerfectionOf_isDeltaHom E 0).comp hj

/-- 全実段の係数像は、既存環余極限内で元のA係数像に一致する。 -/
theorem deltaAlgebraPerfectionOf_comp_coefficient (n : ℕ) :
    (deltaPerfectionOf E n).comp (deltaAlgebraFrobeniusCoefficient E j n) =
      deltaAlgebraPerfectionCoefficient E j := by
  apply RingHom.ext
  intro a
  change deltaPerfectionOf E n ((E.frobeniusLift : B → B)^[n] (j a)) =
    deltaPerfectionOf E 0 (j a)
  simpa only [Nat.sub_zero] using deltaPerfectionOf_iterate E (Nat.zero_le n) (j a)

/-- 既存環完全化への標準段射は、正確な元のA作用について線形。 -/
def deltaAlgebraPerfectionStageMap (n : ℕ) :
    baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) ⟶
      baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j) := by
  let f : baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n) →ₗ[A]
      baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j) :=
    { toFun := fun x => deltaPerfectionOf E n x
      map_add' := (deltaPerfectionOf E n).map_add
      map_smul' := by
        intro a x
        change B at x
        rw [RingHom.id_apply]
        change deltaPerfectionOf E n (deltaAlgebraFrobeniusCoefficient E j n a * x) =
          deltaAlgebraPerfectionCoefficient E j a * deltaPerfectionOf E n x
        rw [map_mul]
        exact congrArg (fun z => z * deltaPerfectionOf E n x)
          (RingHom.congr_fun (deltaAlgebraPerfectionOf_comp_coefficient E j n) a) }
  exact { hom' := f }

/-- A線形段射の値は、既存環余極限の元の標準射そのもの。 -/
theorem deltaAlgebraPerfectionStageMap_apply (n : ℕ)
    (x : baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j n)) :
    (deltaAlgebraPerfectionStageMap E j n).hom x = deltaPerfectionOf E n x := rfl

/-- 隣接する実Frobenius遷移は、環完全化への標準段射と可換。 -/
theorem deltaAlgebraPerfectionStageMap_transition (n : ℕ) :
    deltaAlgebraFrobeniusStageTransition E j n ≫ deltaAlgebraPerfectionStageMap E j (n + 1) =
      deltaAlgebraPerfectionStageMap E j n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change B at x
  change deltaPerfectionOf E (n + 1) (E.frobeniusLift x) = deltaPerfectionOf E n x
  exact deltaPerfectionOf_succ_frobenius E n x

/-- 実環δ完全化の、元のA加群としての標準逐次余錐。 -/
def deltaAlgebraPerfectionModuleCocone :
    Cocone (deltaAlgebraFrobeniusStageModuleDiagram E j) where
  pt := baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j)
  ι := NatTrans.ofSequence (fun n => deltaAlgebraPerfectionStageMap E j n) (by
    intro n
    rw [deltaAlgebraFrobeniusStageModuleDiagram_map_succ]
    exact deltaAlgebraPerfectionStageMap_transition E j n)

/-- 任意二段の実加群図式射は、元の実Frobenius反復を送る。 -/
theorem deltaAlgebraFrobeniusStageModuleDiagram_map_apply {i k : ℕ} (h : i ≤ k)
    (x : baseChangeScalarModule (deltaAlgebraFrobeniusCoefficient E j i)) :
    ((deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE h)).hom x =
      (E.frobeniusLift : B → B)^[k - i] x := by
  induction k, h using Nat.le_induction with
  | base => simp
  | succ k hik ih =>
      have he : homOfLE (Nat.le.step hik) =
          homOfLE hik ≫ homOfLE (Nat.le_succ k) := Subsingleton.elim _ _
      rw [he, Functor.map_comp, deltaAlgebraFrobeniusStageModuleDiagram_map_succ]
      change E.frobeniusLift
        (((deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE hik)).hom x) = _
      rw [ih]
      have hn : k + 1 - i = (k - i) + 1 := by omega
      rw [hn, Function.iterate_succ_apply']

/-- 標準A加群余錐は、既存実δ環完全化を頂点とする本当の逐次colimit。 -/
def deltaAlgebraPerfectionModuleCoconeIsColimit :
    IsColimit (deltaAlgebraPerfectionModuleCocone E j) := by
  let : DirectedSystem (fun _ : ℕ => B)
      (fun i k (_ : i ≤ k) => ((E.frobeniusLift ^ (k - i) : B →+* B) : B → B)) :=
    { map_self := by intro i x; simp
      map_map := by
        intro k l i hil hlk x
        change (E.frobeniusLift : B → B)^[k-l]
          ((E.frobeniusLift : B → B)^[l-i] x) = (E.frobeniusLift : B → B)^[k-i] x
        rw [← Function.iterate_add_apply]
        congr 1
        omega }
  let : PreservesFilteredColimitsOfSize.{0, 0} (forget (ModuleCat.{u} A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  let : ReflectsColimit (deltaAlgebraFrobeniusStageModuleDiagram E j)
      (forget (ModuleCat.{u} A)) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  apply isColimitOfReflects (forget (ModuleCat.{u} A))
  apply Types.FilteredColimit.isColimitOf'
  · intro y
    change DeltaPerfection E at y
    obtain ⟨n, x, rfl⟩ := Ring.DirectLimit.exists_of y
    exact ⟨n, x, rfl⟩
  · intro i x y hxy
    change B at x y
    change deltaPerfectionOf E i x = deltaPerfectionOf E i y at hxy
    have hz : deltaPerfectionOf E i (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨k, hik, hk⟩ := Ring.DirectLimit.of.zero_exact
      (G := fun _ : ℕ => B)
      (f' := fun (i k : ℕ) (_ : i ≤ k) => E.frobeniusLift ^ (k-i)) (i := i) (x := x-y) hz
    refine ⟨k, homOfLE hik, ?_⟩
    change ((deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE hik)).hom x =
      ((deltaAlgebraFrobeniusStageModuleDiagram E j).map (homOfLE hik)).hom y
    rw [deltaAlgebraFrobeniusStageModuleDiagram_map_apply,
      deltaAlgebraFrobeniusStageModuleDiagram_map_apply]
    change (E.frobeniusLift ^ (k-i)) x = (E.frobeniusLift ^ (k-i)) y
    exact sub_eq_zero.mp (by simpa only [map_sub] using hk)

/-- 実圏論的加群colimitは、元のA作用を持つ既存実δ完全化と同型。 -/
def deltaAlgebraPerfectionModuleColimitIso :
    colimit (deltaAlgebraFrobeniusStageModuleDiagram E j) ≅
      baseChangeScalarModule (deltaAlgebraPerfectionCoefficient E j) :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (deltaAlgebraPerfectionModuleCoconeIsColimit E j)

/-- 標準colimit同型は、各実Frobenius段から既存環完全化への標準射を保つ。 -/
theorem deltaAlgebraPerfectionModuleColimitIso_ι (n : ℕ) :
    colimit.ι (deltaAlgebraFrobeniusStageModuleDiagram E j) n ≫
      (deltaAlgebraPerfectionModuleColimitIso E j).hom = deltaAlgebraPerfectionStageMap E j n :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (deltaAlgebraPerfectionModuleCoconeIsColimit E j) n

end SerrePositivity.BhattScholze
