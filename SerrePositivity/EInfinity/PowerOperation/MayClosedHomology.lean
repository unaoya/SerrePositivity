module

public import SerrePositivity.EInfinity.PowerOperation.MayClosedCycles
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# May の全整数次数の閉元のホモロジー類

May, Proposition 2.3 の代表元独立性の前段。
元の閉元の kernel と実 cycles・homology を比較し、零類を元の境界で検出する。
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {k : Type u} [CommRing k]

/-- 元の整数次数の閉元と実 cycles の指定同型。 -/
def mayClosedCyclesIso (K : Complex k) (i : ℤ) :
    ModuleCat.of k (MayClosed K i) ≅ K.cycles i :=
  (K.sc' (i - 1) i (i + 1)).moduleCatCyclesIso.symm ≪≫
    (K.cyclesIsoSc' (i - 1) i (i + 1) (by simp [CochainComplex.prev])
      (by simp [CochainComplex.next])).symm

@[reassoc]
lemma mayClosedCyclesIso_i (K : Complex k) (i : ℤ) :
    (mayClosedCyclesIso K i).hom ≫ K.iCycles i =
      (K.sc' (i - 1) i (i + 1)).moduleCatLeftHomologyData.i := by
  simp [mayClosedCyclesIso]

/-- 元のホモロジーと、閉元の境界による商の指定同型。 -/
def mayClosedQuotientIso (K : Complex k) (i : ℤ) :
    K.homology i ≅ (K.sc' (i - 1) i (i + 1)).moduleCatLeftHomologyData.H :=
  K.homologyIsoSc' (i - 1) i (i + 1) (by simp [CochainComplex.prev])
    (by simp [CochainComplex.next]) ≪≫
      (K.sc' (i - 1) i (i + 1)).moduleCatHomologyIso

/-- 同じ閉元の実ホモロジー類。 -/
def mayClosedClass (K : Complex k) (i : ℤ) : MayClosed K i →ₗ[k] K.homology i :=
  ((K.sc' (i - 1) i (i + 1)).moduleCatLeftHomologyData.π ≫
    (mayClosedQuotientIso K i).inv).hom

@[reassoc]
lemma mayClosedCyclesIso_π (K : Complex k) (i : ℤ) :
    (mayClosedCyclesIso K i).hom ≫ K.homologyπ i = ModuleCat.ofHom (mayClosedClass K i) := by
  simp only [mayClosedCyclesIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    mayClosedClass, mayClosedQuotientIso, Iso.trans_inv, ModuleCat.ofHom_hom]
  rw [← HomologicalComplex.π_homologyIsoSc'_inv,
    ShortComplex.moduleCatCyclesIso_inv_π_assoc]

lemma mayClosedClass_surjective (K : Complex k) (i : ℤ) :
    Function.Surjective (mayClosedClass K i) := by
  change Function.Surjective ((mayClosedQuotientIso K i).inv ∘
    (K.sc' (i - 1) i (i + 1)).moduleCatToCycles.range.mkQ)
  exact ((ModuleCat.epi_iff_surjective _).mp
    (inferInstance : Epi (mayClosedQuotientIso K i).inv)).comp (Submodule.mkQ_surjective _)

/-- 零類であることは、同じ元の複体の境界であることと同値。 -/
lemma mayClosedClass_eq_zero_iff (K : Complex k) (i : ℤ) (a : MayClosed K i) :
    mayClosedClass K i a = 0 ↔ ∃ b : K.X (i - 1), K.d (i - 1) i b = a.val := by
  have hi : Function.Injective (mayClosedQuotientIso K i).inv :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  change (mayClosedQuotientIso K i).inv
    ((K.sc' (i - 1) i (i + 1)).moduleCatToCycles.range.mkQ a) = 0 ↔ _
  constructor
  · intro ha
    have hq : (K.sc' (i - 1) i (i + 1)).moduleCatToCycles.range.mkQ a = 0 :=
      hi (ha.trans (map_zero (mayClosedQuotientIso K i).inv.hom).symm)
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
    exact ⟨b, congrArg Subtype.val hb⟩
  · rintro ⟨b, hb⟩
    have ha : a ∈ (K.sc' (i - 1) i (i + 1)).moduleCatToCycles.range :=
      ⟨b, Subtype.ext hb⟩
    have hq : (K.sc' (i - 1) i (i + 1)).moduleCatToCycles.range.mkQ a = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ha
    exact (congrArg (fun z => (mayClosedQuotientIso K i).inv z) hq).trans
      (map_zero (mayClosedQuotientIso K i).inv.hom)

/-- 閉元の次数の移送は、実ホモロジーの同じ次数の移送と両立する。 -/
lemma mayClosedClass_index (K : Complex k) {i j : ℤ} (h : i = j) (a : MayClosed K i) :
    mayClosedClass K j (mayClosedIndex K h a) =
      (eqToHom (congrArg (fun i : ℤ => K.homology i) h)).hom (mayClosedClass K i a) := by
  subst j
  rfl

/-- 全ての実ホモロジー類の指定閉代表。 -/
def mayClosedRepresentative (K : Complex k) (i : ℤ) (x : K.homology i) : MayClosed K i :=
  Classical.choose (mayClosedClass_surjective K i x)

lemma mayClosedRepresentative_spec (K : Complex k) (i : ℤ) (x : K.homology i) :
    mayClosedClass K i (mayClosedRepresentative K i x) = x :=
  Classical.choose_spec (mayClosedClass_surjective K i x)

/-- 同じ閉元のホモロジー類は全複体射に自然。 -/
lemma mayClosedClass_naturality {K L : Complex k} (f : K ⟶ L) (i : ℤ)
    (a : MayClosed K i) :
    homologyMap f i (mayClosedClass K i a) = mayClosedClass L i (mayClosedMap f i a) := by
  have hc : cyclesMap f i ((mayClosedCyclesIso K i).hom a) =
      (mayClosedCyclesIso L i).hom (mayClosedMap f i a) := by
    apply (ModuleCat.mono_iff_injective (L.iCycles i)).mp inferInstance
    calc
      _ = f.f i (K.iCycles i ((mayClosedCyclesIso K i).hom a)) :=
        congrArg (fun m => m ((mayClosedCyclesIso K i).hom a)) (cyclesMap_i f i)
      _ = f.f i a.val :=
        congrArg (f.f i) (congrArg (fun m => m a) (mayClosedCyclesIso_i K i))
      _ = _ := (congrArg (fun m => m (mayClosedMap f i a)) (mayClosedCyclesIso_i L i)).symm
  change homologyMap f i ((ModuleCat.ofHom (mayClosedClass K i)) a) =
    (ModuleCat.ofHom (mayClosedClass L i)) (mayClosedMap f i a)
  rw [← mayClosedCyclesIso_π, ← mayClosedCyclesIso_π]
  change homologyMap f i (K.homologyπ i ((mayClosedCyclesIso K i).hom a)) =
    L.homologyπ i ((mayClosedCyclesIso L i).hom (mayClosedMap f i a))
  have h := congrArg (fun m => m ((mayClosedCyclesIso K i).hom a)) (homologyπ_naturality f i)
  change homologyMap f i (K.homologyπ i ((mayClosedCyclesIso K i).hom a)) =
    L.homologyπ i (cyclesMap f i ((mayClosedCyclesIso K i).hom a)) at h
  exact h.trans (congrArg (L.homologyπ i) hc)

end SerrePositivity.EInfinity.PowerOperation
