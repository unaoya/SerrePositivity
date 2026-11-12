module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechDouble
public import SerrePositivity.AlgebraicGeometry.CechCoefficientExactness

/-!
概要：増大 Čech の完全性を、実際の二重図式の行・列から取り出す。
方針：増大項の核と正長のサイクルの前像を、微分の完全性にまとめる。
規約：任意の係数前層の補助述語。最終出力の AugmentedRingCechExact は変更しない。
使われ方：有限標準細分からアフィン被覆の完全性を得る B1 の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R) (U : ι → Opens X)

/-- 係数前層の増大 Čech の完全性を表す補助の述語。 -/
structure OpenCoverCechAcyclic : Prop where
  injective_zero : Function.Injective (fullCechDifferential (openCoverCechDiagram P U) 0)
  exact : ∀ k, Function.Exact (fullCechDifferential (openCoverCechDiagram P U) k)
    (fullCechDifferential (openCoverCechDiagram P U) (k + 1))

/-- 係数前層の自然同型を有限交叉の係数図式へ移す。 -/
def openCoverCechCoefficientIso {Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R} (e : P ≅ Q) :
    openCoverCechDiagram P U ≅ openCoverCechDiagram Q U :=
  NatIso.ofComponents (fun T ↦ e.app (op (cechOpenIntersection U T)))
    (fun h ↦ e.hom.naturality _)

/-- 自然同型な係数前層へ、増大 Čech の完全性を移す。 -/
theorem openCoverCechAcyclic_of_iso {Q : (Opens X)ᵒᵖ ⥤ ModuleCat.{v} R}
    (e : P ≅ Q) (h : OpenCoverCechAcyclic P U) : OpenCoverCechAcyclic Q U where
  injective_zero := fullCechCoefficientEquiv_zero_injective
    (openCoverCechCoefficientIso P U e) h.injective_zero
  exact k := fullCechCoefficientEquiv_exact (openCoverCechCoefficientIso P U e) k (h.exact k)

/-- 増大項の核の消滅と、正長の各サイクルの前像から完全性を得る。 -/
theorem openCoverCechAcyclic_of_cycles
    (hzero : ∀ x, fullCechDifferential (openCoverCechDiagram P U) 0 x = 0 → x = 0)
    (hbound : ∀ k x, fullCechDifferential (openCoverCechDiagram P U) (k + 1) x = 0 →
      ∃ y, fullCechDifferential (openCoverCechDiagram P U) k y = x) :
    OpenCoverCechAcyclic P U := by
  constructor
  · intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  · intro k x
    constructor
    · exact hbound k x
    · rintro ⟨y, rfl⟩
      exact LinearMap.congr_fun (fullCechAugmentedDifferential_squared
        (openCoverCechDiagram P U) k) y

variable (V : κ → Opens X)

/-- 二重 Čech の零番の行の完全性から、元の前層の Čech 完全性を得る。 -/
theorem openCoverCechAcyclic_of_double_zero_row
    (h : SerrePositivity.Cech.RowExact (openCoverCechDoubleTerm P U V)
      (openCoverCechDoubleHorizontal P U V) 0) : OpenCoverCechAcyclic P U := by
  have hres := openCoverCechAcyclic_of_cycles (openCoverCechResolution P V 0) U h.1 h.2
  exact openCoverCechAcyclic_of_iso (openCoverCechResolution P V 0) U
    (openCoverCechResolutionZeroIso P V) hres

/-- 全空間との交叉を取る前層は、元の前層と自然に同型。 -/
def openCoverIntersectionPresheafTopIso : openCoverIntersectionPresheaf P ⊤ ≅ P :=
  NatIso.ofComponents (fun O ↦ P.mapIso (eqToIso (congrArg op (show (⊤ : Opens X) ⊓ O.unop = O.unop by simp)))) (by
    intro O O' h
    change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
    rw [← P.map_comp, ← P.map_comp]
    congr 1)

/-- 元の前層の Čech 完全性から、二重図式の零番の列の完全性を得る。 -/
theorem openCoverCechDouble_zero_col_exact (h : OpenCoverCechAcyclic P V) :
    SerrePositivity.Cech.ColExact (openCoverCechDoubleTerm P U V)
      (openCoverCechDoubleVertical P U V) 0 := by
  have htop := openCoverCechAcyclic_of_iso P V (openCoverIntersectionPresheafTopIso P).symm h
  apply openCoverCechDouble_colExact P U V 0
  · intro t
    have he : cechOpenIntersection U (cechTupleSupport t) = ⊤ := by
      rw [cechTupleSupport_empty]
      simp [cechOpenIntersection]
    let e := eqToIso (congrArg
      (fun W ↦ openCoverCechDiagram (openCoverIntersectionPresheaf P W) V) he)
    exact fullCechCoefficientEquiv_zero_injective e.symm htop.injective_zero
  · intro t j
    have he : cechOpenIntersection U (cechTupleSupport t) = ⊤ := by
      rw [cechTupleSupport_empty]
      simp [cechOpenIntersection]
    let e := eqToIso (congrArg
      (fun W ↦ openCoverCechDiagram (openCoverIntersectionPresheaf P W) V) he)
    exact fullCechCoefficientEquiv_exact e.symm j (htop.exact j)

/-- 細分の完全性と各交叉上の完全性から、元の被覆の増大 Čech 完全性を得る。 -/
theorem openCoverCechAcyclic_of_refinement
    (ρ : κ → ι) (hρ : ∀ i, V i ≤ U (ρ i)) (hV : OpenCoverCechAcyclic P V)
    (hinter : ∀ (i : ℕ), 0 < i → ∀ t : Fin i → ι,
      OpenCoverCechAcyclic (openCoverIntersectionPresheaf P
        (cechOpenIntersection U (cechTupleSupport t))) V) : OpenCoverCechAcyclic P U := by
  apply openCoverCechAcyclic_of_double_zero_row P U V
  apply (openCoverCechDouble_exact_zero_iff P U V
    (openCoverCechDouble_rowExact P U V ρ hρ) ?_).mpr
    (openCoverCechDouble_zero_col_exact P U V hV)
  intro i hi
  exact openCoverCechDouble_colExact P U V i
    (fun t ↦ (hinter i hi t).injective_zero) (fun t j ↦ (hinter i hi t).exact j)

end SerrePositivity.AlgebraicGeometry
