module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.ModulePiTransport
public import SerrePositivity.InfinityCategories.Derived.ModulePiMooreNaturality
public import SerrePositivity.InfinityCategories.Derived.ModulePiZeroMoore
/-!
概要：単体的加群の全基点の正次数 π を Moore ホモロジーへ自然に同定する。
方針：加法平行移動の逆と零基点の Moore 比較を合成する。
規約：次数は n+1。任意指定道による移送は同じホモロジー元で検出する。
使われ方：評価ホモロジー余錐から橋の各元ごとの条件を導く。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory AlgebraicTopology Opposite SSet
open SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R]
  (W : SimplicialObject (ModuleCat.{v} R)) [KanComplex (moduleUnderlyingSSet W)]

/-- 全基点での π_{n+1} と、同じ正規化 Moore 複体の H_{n+1}。 -/
def dgBarCompactModulePiHomologyEquiv (n : ℕ) (x : W.obj (op ⦋0⦌)) :
    KanHomotopyGroup (moduleUnderlyingSSet W) n x ≃*
      Multiplicative (((normalizedMooreComplex (ModuleCat.{v} R)).obj W).homology (n + 1)) :=
  (KanHomotopyGroup.equivOfIso n (moduleTranslationIso W x)
    (moduleTranslationIso_zero W x)).symm.trans (modulePiMooreGroupEquiv W n)

variable {W} {V : SimplicialObject (ModuleCat.{v} R)} [KanComplex (moduleUnderlyingSSet V)]

lemma dgBarCompactModulePiHomologyEquiv_naturality
    (f : W ⟶ V) (n : ℕ) (x : W.obj (op ⦋0⦌))
    (a : KanHomotopyGroup (moduleUnderlyingSSet W) n x) :
    dgBarCompactModulePiHomologyEquiv V n ((f.app (op ⦋0⦌)).hom x)
        (dgBarCompactPiMap n (moduleUnderlyingSSetMap f) x a) =
      (HomologicalComplex.homologyMap ((normalizedMooreComplex (ModuleCat.{v} R)).map f)
        (n + 1)).hom (dgBarCompactModulePiHomologyEquiv W n x a) := by
  obtain ⟨a₀, rfl⟩ := (KanHomotopyGroup.equivOfIso n (moduleTranslationIso W x)
    (moduleTranslationIso_zero W x)).surjective a
  change dgBarCompactModulePiHomologyEquiv V n _
    (KanHomotopyGroup.map (moduleUnderlyingSSetMap f) rfl _) = _
  rw [moduleTranslationIso_pi_naturality]
  simp only [dgBarCompactModulePiHomologyEquiv, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  let e := KanHomotopyGroup.equivOfIso n
    (moduleTranslationIso V ((f.app (op ⦋0⦌)).hom x))
    (moduleTranslationIso_zero V ((f.app (op ⦋0⦌)).hom x))
  change (modulePiMooreGroupEquiv V n)
    (e.symm (e (KanHomotopyGroup.map (moduleUnderlyingSSetMap f)
      (moduleUnderlyingSSetMap_zero f) a₀))) = _
  rw [MulEquiv.symm_apply_apply]
  exact modulePiMooreGroupEquiv_naturality f n a₀

lemma dgBarCompactModulePiTransport_of_homology_eq (n : ℕ)
    {x y : W.obj (op ⦋0⦌)} (e : (moduleUnderlyingSSet W).Edge x y)
    (a : KanHomotopyGroup (moduleUnderlyingSSet W) n x)
    (b : KanHomotopyGroup (moduleUnderlyingSSet W) n y)
    (h : dgBarCompactModulePiHomologyEquiv W n x a =
      dgBarCompactModulePiHomologyEquiv W n y b) : dgBarCompactPiTransport n e a b := by
  let ex := KanHomotopyGroup.equivOfIso n (moduleTranslationIso W x)
    (moduleTranslationIso_zero W x)
  let ey := KanHomotopyGroup.equivOfIso n (moduleTranslationIso W y)
    (moduleTranslationIso_zero W y)
  have h₀ : ex.symm a = ey.symm b := (modulePiMooreGroupEquiv W n).injective h
  have hb : ey (ex.symm a) = b := by
    apply ey.symm.injective
    simpa only [MulEquiv.symm_apply_apply] using h₀
  rw [← hb]
  have ht := dgBarCompactModulePiTransport W n e (ex.symm a)
  change dgBarCompactPiTransport n e (ex (ex.symm a)) (ey (ex.symm a)) at ht
  rw [MulEquiv.apply_symm_apply] at ht
  exact ht

end SerrePositivity.InfinityCategories
