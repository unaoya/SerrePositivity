module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Milnor.ArcMilnorDetection
public import SerrePositivity.BhattScholze.Perfectoidization.Arc.Descent.ArcPerfectCech

/-!
## 概要
Milnor 四角形での Čech 完全性の検出。
## 方針
底変換後の増大複体とテンソル後の複体を比較し、次数ごとに Tor 消滅を使う。
## 規約
三つの角は局所化、商、剰余体。平坦性は仮定しない。
## 使われ方
BM18 Proposition 4.8 の証明 (5) の一点で交わる区間。
-/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped Simplicial

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

set_option backward.isDefEq.respectTransparency false

variable {V : Type u} [CommRing V]

/-- 任意の底変換で、環の Čech 完全性は元の増大複体をテンソルした完全性と同値。 -/
theorem cechExact_baseChange_iff_tensorCochain (B : Under (CommRingCat.of V))
    (D : Type u) [CommRing D] [Algebra V D] :
    Cech.IsCechExact
      (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of V) (CommRingCat.of D)).obj B).hom) ↔
    (tensorCochain (Cech.moduleCech B) (ModuleCat.of V D)).Acyclic := by
  let F := forget₂ (ModuleCat.{u} V) AddCommGrpCat.{u}
  let T := tensorLeft (ModuleCat.of V D)
  let K := Cech.moduleCech B
  have hF (S : ShortComplex (ModuleCat.{u} V)) : (S.map F).Exact ↔ S.Exact := by
    rw [ShortComplex.ab_exact_iff_function_exact,
      ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    rfl
  let e := (Functor.mapHomologicalComplexCompIso (Iso.refl (T ⋙ F)) (.up ℕ)).app K
  let q := Cech.baseChangeCochainIso (CommRingCat.of D) B
  have e' := e.symm ≪≫ q
  change Cech.AugmentedRingCechExact _ ↔ _
  rw [Cech.ringCechExact_iff_acyclic, ← Cech.acyclic_map_iff_of_exact F _ hF]
  exact ⟨fun h n => (h n).of_iso e'.symm, fun h n => (h n).of_iso e'⟩

/-- 完全標数 p の Čech 項と完全係数の間の正次数 Tor は消滅する。 -/
theorem moduleCech_tor_subsingleton (B : Under (CommRingCat.of V))
    (D : Type u) [CommRing D] [Algebra V D] (p : ℕ) [Fact p.Prime]
    [PerfectRing V p] [PerfectRing B.right p] [PerfectRing D p] (hp : (p : V) = 0)
    (i : ℕ) (hi : 0 < i) (n : ℕ) :
    Subsingleton (TorModule V i ((Cech.moduleCech B).X n) D) := by
  cases n with
  | zero =>
    change Subsingleton (TorModule V i V D)
    exact perfectRing_tor_subsingleton_of_char_eq_zero p V hp V D i hi
  | succ n =>
    let T := (Cech.underCech B).right.obj ⦋n⦌
    let : Algebra V T := RingHom.toAlgebra T.hom.hom
    change Subsingleton (TorModule V i T D)
    let : PerfectRing (Arrow.mk B.hom).left p := ‹PerfectRing V p›
    let : PerfectRing (Arrow.mk B.hom).right p := ‹PerfectRing B.right p›
    let : PerfectRing T p := Cech.cechConerve_perfectRing p (Arrow.mk B.hom) hp ⦋n⦌
    exact perfectRing_tor_subsingleton_of_char_eq_zero p V hp T D i hi

/-- 付値環の Milnor 四角形の三つの角上の Čech 完全性が元の完全性を検出する
（BM18 Proposition 4.8 の証明 (5) の、交わりが一点の場合）。 -/
theorem cechExact_of_milnorTensor [IsDomain V] [ValuationRing V] (P : Ideal V) [P.IsPrime]
    (B : Under (CommRingCat.of V)) (p : ℕ) [Fact p.Prime]
    [PerfectRing V p] [PerfectRing B.right p] (hp : (p : V) = 0)
    (hl : Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of V)
      (CommRingCat.of (Localization.AtPrime P))).obj B).hom))
    (hq : Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of V)
      (CommRingCat.of (V ⧸ P))).obj B).hom))
    (hr : Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of V)
      (CommRingCat.of P.ResidueField)).obj B).hom)) :
    Cech.IsCechExact (Arrow.mk B.hom) := by
  apply (Cech.moduleCech_acyclic_iff B).mp
  apply acyclic_of_milnorTensor P (Cech.moduleCech B) ?_
    ((cechExact_baseChange_iff_tensorCochain B _).mp hl)
    ((cechExact_baseChange_iff_tensorCochain B _).mp hq)
    ((cechExact_baseChange_iff_tensorCochain B _).mp hr)
  let := perfectRing_primeResidue P p hp
  exact moduleCech_tor_subsingleton B P.ResidueField p hp 1 (by decide)

end SerrePositivity.BhattScholze.Perfectoidization.Derived

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Prop 8.10" (partial := component) "BM18 の経路 B（BS-W12）の B1〜B5 は本体。組み立て B6 は ⑥ の BS17 Thm 4.1 (i) 待ち ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.cechExact_of_milnorTensor
