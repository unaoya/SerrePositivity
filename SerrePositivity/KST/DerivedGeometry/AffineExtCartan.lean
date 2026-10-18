module

public import SerrePositivity.KST.DerivedGeometry.FreeFormalExt
public import SerrePositivity.KST.DerivedGeometry.AffineSheafExtVanishing
public import SerrePositivity.KST.DerivedGeometry.RelativeAffineCech

/-!
概要：有限基本開 Čech の完全性から基本開上の自由層を始域とする Ext の消滅を導く。
方針：局所消滅する有限被覆を選び、自由 Čech 分解による有限次元移動と強帰納を使う。
規約：非有界全複体化や収束の仮定を用いない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン消滅。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace PrimeSpectrum Abelian
open scoped Simplicial
namespace SerrePositivity.KST.DerivedGeometry
variable {A R : Type u} [CommRing A] [Ring R]

/--
概要：有限基本開 Čech の正次数完全性から各基本開の正次数 Ext は零。
方針：低次数の消滅を有限交叉と有限余積へ移し、局所零の類の Čech 制限の単射性を使う。
規約：Čech 完全性は全基本開の被覆について明示的に要求する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の Cartan 型判定。
-/
lemma affineExt_subsingleton_of_cech
    (F : Sheaf (Opens.grothendieckTopology (PrimeSpectrum A)) (ModuleCat.{u} R))
    (hcech : ∀ (ι : Type u) [Finite ι] (a : A) (f : ι → A),
      (⨆ i, basicOpen (f i)) = basicOpen a → ∀ m : ℕ,
        ((cechComplexFunctor (fun i => basicOpen (f i))).obj
          (F.obj ⋙ forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).ExactAt (m + 1))
    (n : ℕ) (a : A) :
    Subsingleton (Ext ((freeModuleSheafOnOpen R (TopCat.of (PrimeSpectrum A))).obj
      (basicOpen a)) F (n + 1)) := by
  classical
  induction n using Nat.strong_induction_on generalizing a with
  | h n ih =>
    apply subsingleton_of_forall_eq 0
    intro α
    let X := TopCat.of (PrimeSpectrum A)
    let L := freeModuleSheafOnOpen R X
    obtain ⟨s, f, hf, hcover, hα⟩ := moduleSheafExt_finiteBasicOpenVanishing F n
      (basicOpen a) (isCompact_basicOpen a) α
    let U := fun i : s => basicOpen (f i)
    let K := relativeFreeFormalSheafAugmentedCechComplex R X U (basicOpen a) hf
    let e := freeFormalSheafInclIso R X (basicOpen a)
    let α₀ : Ext (K.X 0) F (n + 1) := (Ext.mk₀ e.hom).comp α (zero_add (n + 1))
    have hvan (i q : ℕ) (hq : 0 < q) (hqn : q < n + 1) :
        Subsingleton (Ext (K.X (i + 1)) F q) := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
      change Subsingleton (Ext ((freeFormalSheafFunctor R X).obj
        ((FormalCoproduct.mk s U).cech.obj (.op ⦋i⦌))) F (m + 1))
      letI : Finite ((FormalCoproduct.mk s U).cech.obj (.op ⦋i⦌)).I :=
        inferInstanceAs (Finite (Fin (i + 1) → s))
      apply freeFormalSheaf_ext_subsingleton R X
      intro t
      change Subsingleton (Ext (L.obj (∏ᶜ fun j : Fin (i + 1) => basicOpen (f (t j)))) F (m + 1))
      rw [basicOpen_finiteProduct (R := CommRingCat.of A)]
      exact ih m (by omega) (∏ j : Fin (i + 1), f (t j))
    have hres : (Ext.mk₀ (K.d 1 0)).comp α₀ (zero_add (n + 1)) = 0 := by
      change (Ext.mk₀ ((freeFormalSheafFunctor R X).map
        ((boundedOpenCechAugmented U (basicOpen a) hf).hom.app (.op ⦋0⦌)))).comp
          ((Ext.mk₀ e.hom).comp α (zero_add (n + 1))) (zero_add (n + 1)) = 0
      letI : Finite ((FormalCoproduct.mk s U).cech.obj (.op ⦋0⦌)).I :=
        inferInstanceAs (Finite (Fin 1 → s))
      apply freeFormalSheaf_point_precomp_eq_zero R X
        ((FormalCoproduct.mk s U).cech.obj (.op ⦋0⦌)) (basicOpen a)
        ((boundedOpenCechAugmented U (basicOpen a) hf).hom.app (.op ⦋0⦌)) F (n + 1) α
      intro t
      change (Ext.mk₀ (L.map (Pi.π _ 0 ≫ homOfLE (hf (t 0))))).comp α
        (zero_add (n + 1)) = 0
      rw [L.map_comp, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero, hα (t 0)]
      exact Ext.comp_zero _ _ _ _ _
    have hz : α₀ = 0 := resolution_ext_eq_zero n K F
      (relativeFreeFormalSheafAugmentedCech_acyclic R X U (basicOpen a) hf hcover)
      (relativeFreeFormalSheafAugmentedCech_homExact R X U (basicOpen a) hf F hcover
        (hcech s a f hcover)) hvan α₀ hres
    let eExt := ((evaluation _ AddCommGrpCat.{u}).obj F).mapIso ((extFunctor (n + 1)).mapIso e.op)
    apply (ConcreteCategory.bijective_of_isIso eExt.hom).injective
    change α₀ = (Ext.mk₀ e.hom).comp 0 (zero_add (n + 1))
    rw [Ext.comp_zero]
    exact hz

end SerrePositivity.KST.DerivedGeometry
