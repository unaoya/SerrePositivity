module

public import SerrePositivity.KST.DerivedGeometry.BasicOpenCechLocalization
public import SerrePositivity.KST.DerivedGeometry.BasicOpenLocalizationR

/-!
概要：アフィン準連接層の有限基本開 Čech 複体の正次数の完全性。
方針：各被覆元で局所化し、最大開集合を含む族の Čech 収縮を用いる。
規約：実際の tilde 層の切断と Mathlib の交代 Čech 微分を使う。
使われ方：TT §3、Bondal–van den Bergh Thm 3.1.1、Toën §3.2 のアフィン計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry PrimeSpectrum
namespace SerrePositivity.KST.DerivedGeometry
variable {R : CommRingCat.{u}}

/--
概要：有限基本開被覆について tilde 層の Čech 複体は全正次数で完全。
方針：局所化との比較同型を経て、被覆元自身を最大要素とする収縮へ移す。
規約：加群の有限生成性も係数の平坦性も要求しない。
使われ方：TT §3、Toën §3.2 のアフィン導来比較への Čech 計算。
-/
lemma affineCech_exactAt (M : ModuleCat.{u} R) {ι : Type u} [Finite ι]
    (f : ι → R) (hcover : (⨆ i, basicOpen (f i)) = ⊤) (n : ℕ) :
    ((cechComplexFunctor (fun i => basicOpen (f i))).obj
      (modulesSpecToSheaf.obj (tilde M)).obj).ExactAt (n + 1) := by
  have hc : (⨆ r : Set.range f, basicOpen r.val) = ⊤ := by
    apply top_unique
    rw [← hcover]
    exact iSup_le (fun i => le_iSup_of_le ⟨f i, ⟨i, rfl⟩⟩ le_rfl)
  apply (basicOpenLocalizationR_exactAt_iff (Set.range f) hc _ (n + 1)).mpr
  intro r
  obtain ⟨j, hj⟩ := r.property
  have hlocal := maximalOpenCech_exactAt
    (fun i => basicOpen (f i) ⊓ basicOpen (f j)) (basicOpen (f j))
    (fun _ => inf_le_right) (modulesSpecToSheaf.obj (tilde M)).obj j (by simp) n
  have he := basicOpenCechLocalizationIso M (f j) f
  have hex := (exactAt_iff_of_quasiIsoAt he.hom (n + 1)).mpr hlocal
  simpa only [hj] using hex

end SerrePositivity.KST.DerivedGeometry
