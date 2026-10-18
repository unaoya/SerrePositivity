module

public import SerrePositivity.KST.DerivedGeometry.AffineCechExact
public import SerrePositivity.KST.DerivedGeometry.RelativeLocalizationExact
public import SerrePositivity.KST.DerivedGeometry.AffineQuasicoherentCech
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
概要：基本開の有限基本開被覆について準連接層の Čech が正次数で完全。
方針：被覆先の定義元の可逆性と相対局所化判定を、既証の局所収縮へ適用する。
規約：全空間の被覆には限定せず、有限生成性や平坦性も要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 のアフィン消滅の帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry PrimeSpectrum
namespace SerrePositivity.KST.DerivedGeometry

/--
概要：各因子で可逆なスカラーは加群圏の実際の積でも可逆。
方針：選ばれた積と関数加群の線形同値を使い、単射性と全射性を成分ごとに示す。
規約：積の添字の有限性は不要。
使われ方：TT §3、Toën §3.2 の Čech 項の基本開定義元の可逆性。
-/
lemma moduleProduct_isUnit_smul {R : Type u} [CommRing R] {ι : Type u}
    (Z : ι → ModuleCat.{u} R) (a : R)
    (h : ∀ i, IsUnit (algebraMap R (Module.End R (Z i)) a)) :
    IsUnit (algebraMap R (Module.End R (∏ᶜ Z : ModuleCat.{u} R)) a) := by
  rw [Module.End.isUnit_iff]
  let e := (ModuleCat.piIsoPi Z).toLinearEquiv
  have hi (i : ι) := (Module.End.isUnit_iff _).mp (h i)
  constructor
  · intro x y hxy
    change a • x = a • y at hxy
    apply e.injective
    funext i
    apply (hi i).injective
    change a • e x i = a • e y i
    simpa only [map_smul, Pi.smul_apply] using congrArg (fun z => e z i) hxy
  · intro y
    choose x hx using fun i => (hi i).surjective (e y i)
    refine ⟨e.symm x, e.injective ?_⟩
    change e (a • e.symm x) = e y
    rw [map_smul, LinearEquiv.apply_symm_apply]
    ext i
    exact hx i

variable {R : CommRingCat.{u}}

/--
概要：D(a) 内の基本開の有限族の Čech の各項で a は可逆に作用する。
方針：各有限交叉が D(a) に含まれることから切断の可逆性を得て積へ移す。
規約：切断に元の R 加群構造を保持する。
使われ方：TT §3、Toën §3.2 の基本開の局所化判定。
-/
lemma affineCech_isUnit_smul (M : ModuleCat.{u} R) {ι : Type u} [Finite ι]
    (a : R) (f : ι → R) (hf : ∀ i, basicOpen (f i) ≤ basicOpen a) (n : ℕ) :
    IsUnit (algebraMap R (Module.End R
      (((cechComplexFunctor (fun i => basicOpen (f i))).obj
        (modulesSpecToSheaf.obj (tilde M)).obj).X n)) a) := by
  apply moduleProduct_isUnit_smul
  intro t
  exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := tilde M) a
    ((leOfHom (Pi.π (fun i : Fin (n + 1) => basicOpen (f (t i))) 0)).trans (hf (t 0)))

/--
概要：D(a) の有限基本開被覆について tilde 層の Čech は正次数で完全。
方針：各被覆元で局所化して最大開による収縮を使い、相対局所化判定で反映する。
規約：非有界の係数加群や非有限生成加群も許す。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の基本開上の消滅。
-/
lemma relativeAffineCech_exactAt (M : ModuleCat.{u} R) {ι : Type u} [Finite ι]
    (a : R) (f : ι → R) (hcover : (⨆ i, basicOpen (f i)) = basicOpen a) (n : ℕ) :
    ((cechComplexFunctor (fun i => basicOpen (f i))).obj
      (modulesSpecToSheaf.obj (tilde M)).obj).ExactAt (n + 1) := by
  have hf (i : ι) : basicOpen (f i) ≤ basicOpen a := by
    rw [← hcover]
    exact le_iSup (fun j : ι => basicOpen (f j)) i
  let K := (cechComplexFunctor (fun i => basicOpen (f i))).obj
    (modulesSpecToSheaf.obj (tilde M)).obj
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  apply relativeBasicOpenLocalization_exact a f hcover
    (ha₁ := affineCech_isUnit_smul M a f hf n)
    (ha₂ := affineCech_isUnit_smul M a f hf (n + 1))
  intro j
  have hlocal := maximalOpenCech_exactAt
    (fun i => basicOpen (f i) ⊓ basicOpen (f j)) (basicOpen (f j))
    (fun _ => inf_le_right) (modulesSpecToSheaf.obj (tilde M)).obj j (by simp) n
  have he := basicOpenCechLocalizationIso M (f j) f
  have hex := (exactAt_iff_of_quasiIsoAt he.hom (n + 1)).mpr hlocal
  exact (HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)).mp hex

/--
概要：任意のアフィン準連接 O 加群層の Čech 複体は全正次数で完全。
方針：大域切断の tilde からの余単位の同型を Čech 関手に適用する。
規約：各項は元の層の実際の切断。
使われ方：TT §3、Toën §3.2 のアフィン非有界導来比較の入力。
-/
lemma relativeAffineQuasicoherentCech_exactAt (N : (Spec R).Modules) [N.IsQuasicoherent]
    {ι : Type u} [Finite ι] (a : R) (f : ι → R) (hcover : (⨆ i, basicOpen (f i)) = basicOpen a)
    (n : ℕ) :
    ((cechComplexFunctor (fun i => basicOpen (f i))).obj
      (modulesSpecToSheaf.obj N).obj).ExactAt (n + 1) := by
  let e := (cechComplexFunctor (fun i => basicOpen (f i))).mapIso
    ((modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _).mapIso (asIso N.fromTildeΓ))
  exact (exactAt_iff_of_quasiIsoAt e.hom (n + 1)).mp
    (relativeAffineCech_exactAt (moduleSpecΓFunctor.obj N) a f hcover n)

/--
概要：アフィン準連接 H 係数加群層の基礎 Čech 複体は全正次数で完全。
方針：係数を忘れた準連接 O 加群層へ前の定理を適用する。
規約：H の可換性・平坦性を要求しない。
使われ方：TT §3、Toën §3.2 の係数版アフィン導来比較の入力。
-/
lemma relativeAffineCoefficientCech_exactAt (H : Type u) [Ring H] [Algebra R H]
    (N : (tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).QCoh)
    {ι : Type u} [Finite ι] (a : R) (f : ι → R) (hcover : (⨆ i, basicOpen (f i)) = basicOpen a)
    (n : ℕ) :
    ((cechComplexFunctor (fun i => basicOpen (f i))).obj
      (modulesSpecToSheaf.obj
        ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj N.obj)).obj).ExactAt
          (n + 1) := by
  let : ((tensorCoefficientSheaf H (Scheme.ΓSpecIso R).inv.hom).forget.obj
    N.obj).IsQuasicoherent := N.property
  exact relativeAffineQuasicoherentCech_exactAt _ a f hcover n


end SerrePositivity.KST.DerivedGeometry
