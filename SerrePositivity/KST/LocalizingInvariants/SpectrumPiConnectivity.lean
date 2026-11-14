module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.LocalizingInvariants.ProSpectrumPiConnectivity

/-!
概要：実 Sp 値と射の整数 π による連結度条件を定義し、レベル射の pro 判定へ移す。
方針：各次数の単射・全射から、同じ段を使う eventual 核・像の証人を構成する。
規約：全ての対象と写像は元の h Sp。使われ方：k-connective 条件のレベル毎の適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.LocalizingInvariants.SpectrumHo

def IsPiConnective (X : hoFunctor.obj Sp.{u}) (n : ℤ) : Prop :=
  ∀ j : ℤ, j < n → Subsingleton ((piFunctor j).obj X)

def IsPiConnected {X Y : hoFunctor.obj Sp.{u}} (f : X ⟶ Y) (n : ℤ) : Prop :=
  (∀ j : ℤ, j < n → Function.Injective ((piFunctor j).map f).hom) ∧
    ∀ j : ℤ, j ≤ n → Function.Surjective ((piFunctor j).map f).hom

def IsPiZeroIso {X Y : hoFunctor.obj Sp.{u}} (f : X ⟶ Y) : Prop :=
  Function.Bijective ((piFunctor 0).map f).hom

lemma IsPiConnected.piZeroIso {X Y : hoFunctor.obj Sp.{u}} {f : X ⟶ Y} {n : ℤ}
    (h : IsPiConnected f n) (hn : 1 ≤ n) : IsPiZeroIso f :=
  ⟨h.1 0 (by omega), h.2 0 (by omega)⟩

end SpectrumHo
namespace ProSpectrum

lemma piProConnected_of_levelwise {X Y : Tower.{u}} (f : LevelHom X Y) (n : ℤ)
    (h : ∀ m, SpectrumHo.IsPiConnected (f.app m) n) : IsPiProConnected f n := by
  constructor
  · intro j hj m
    refine ⟨m, le_refl m, fun x hx ↦ ?_⟩
    have hx' : x = 1 := (h m).1 j hj (hx.trans (map_one _).symm)
    subst x
    exact map_one _
  · intro j hj m
    refine ⟨m, le_refl m, fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := (h m).2 j hj y
    refine ⟨x, ?_⟩
    change ((SpectrumHo.piFunctor j).map (f.app m)).hom x =
      ((groups Y j).transition (le_refl m)).hom y
    rw [(groups Y j).transition_self]
    exact hx

end ProSpectrum
end SerrePositivity.KST.LocalizingInvariants

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite LT "Def 2.1" (partial := component) "仮定：Sp のホモトピー圏と整数次数、整数係数（Lean が強い）。結論：π の零・単射・全射による対象と射の連結度を定義。Λ 係数と正方形の連結度を含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.SpectrumHo.IsPiConnected
attribute [cite LT "Def 2.1" (partial := component) "仮定：Sp のホモトピー圏と整数次数、整数係数（Lean が強い）。結論：π の零・単射・全射による対象と射の連結度を定義。Λ 係数と正方形の連結度を含まない（Lean が弱い）。"] _root_.SerrePositivity.KST.LocalizingInvariants.SpectrumHo.IsPiConnective
