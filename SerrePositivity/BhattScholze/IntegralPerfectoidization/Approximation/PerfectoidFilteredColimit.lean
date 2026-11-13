module


public meta import SerrePositivity.Util.Citation
public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import SerrePositivity.BhattScholze.Andre.Transfinite.Limit
public import SerrePositivity.BhattScholze.Perfectoidization.Derived.Interface

/-!
# perfectoid 環の filtered 余極限の完備化

## 概要
BS 著者版 Theorem 10.11 の証明で用いる filtered 余極限の完備化を扱う。

## 方針
共終な有向半順序を一段以降に制限し、環の有向余極限の perfectoid 性と
有界 p 冪ねじれの結果を適用する。

## 規約
添字圏と環は同じ宇宙に置く。完備化は界面の H⁰ 環で表す。

## 使われ方
整代数の perfectoid 化を有限表示有限代数から組み立てる。
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.BhattScholze.Perfectoidization.Derived

open PerfectoidizationInterface SerrePositivity.DerivedCompletion
open SerrePositivity.BhattScholze.Andre.Transfinite

attribute [local instance] HasDerivedCategory.standard

private theorem exists_final_directed_orderBot (I : Type u) [SmallCategory I] [IsFiltered I] :
    ∃ (J : Type u) (_ : PartialOrder J) (_ : IsDirectedOrder J) (_ : OrderBot J)
      (G : J ⥤ I), G.Final := by
  obtain ⟨K, _, hK, hn, F, hf⟩ := IsFiltered.exists_directed I
  let : IsDirectedOrder K := hK
  let k₀ : K := hn.some
  let J := Set.Ici k₀
  let : IsDirectedOrder J := ⟨fun x y => by
    obtain ⟨z, hx, hy⟩ := exists_ge_ge (x : K) (y : K)
    exact ⟨⟨z, x.property.trans hx⟩, hx, hy⟩⟩
  let hmon : Monotone (Subtype.val : J → K) := fun _ _ h => h
  let : hmon.functor.Final := (hmon.final_functor_iff).mpr fun k => by
    obtain ⟨z, hk₀, hk⟩ := exists_ge_ge k₀ k
    exact ⟨⟨z, hk₀⟩, hk⟩
  exact ⟨J, inferInstance, inferInstance, inferInstance, hmon.functor ⋙ F, inferInstance⟩

private def ringDirectLimitIso {J : Type u} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (F : J ⥤ CommRingCat.{u}) (f : ∀ i j, i ≤ j → F.obj i →+* F.obj j)
    (hf : ∀ i j h, f i j h = (F.map (homOfLE h)).hom)
    [DirectedSystem (fun i => F.obj i) (fun i j h => f i j h)]
    (c : Cocone F) (hc : IsColimit c) :
    CommRingCat.of (Ring.DirectLimit (fun i => F.obj i) (fun i j h => f i j h)) ≅ c.pt := by
  let R (i : J) : Type u := F.obj i
  let m (i j : J) (h : i ≤ j) (x : R i) : R j := f i j h x
  let L := Ring.DirectLimit R m
  let φ : L →+* c.pt := Ring.DirectLimit.lift R m c.pt
    (fun i => (c.ι.app i).hom) (fun i j h x => by
      change (c.ι.app j).hom (f i j h x) = (c.ι.app i).hom x
      rw [hf]
      exact RingHom.congr_fun (congrArg (fun q : F.obj i ⟶ c.pt => q.hom) (c.w (homOfLE h))) x)
  have hφ (i : J) (x : R i) : φ (Ring.DirectLimit.of R m i x) = (c.ι.app i).hom x :=
    Ring.DirectLimit.lift_of (G := R) (f := m) c.pt _ _ i x
  let T := forget CommRingCat
  have ht := isColimitOfPreserves T hc
  have hbij : Function.Bijective φ := by
    constructor
    · intro x y he
      obtain ⟨i, a, rfl⟩ := Ring.DirectLimit.exists_of x
      obtain ⟨j, b, rfl⟩ := Ring.DirectLimit.exists_of y
      simp only [hφ] at he
      have hEq : ((T.mapCocone c).ι.app i) a = ((T.mapCocone c).ι.app j) b := he
      obtain ⟨k, u, v, huv⟩ := (Types.FilteredColimit.isColimit_eq_iff (F ⋙ T) ht).mp hEq
      change (F.map u).hom a = (F.map v).hom b at huv
      have hu : m i k (leOfHom u) a = (F.map u).hom a :=
        RingHom.congr_fun (hf i k (leOfHom u)) a
      have hv : m j k (leOfHom v) b = (F.map v).hom b :=
        RingHom.congr_fun (hf j k (leOfHom v)) b
      calc
        Ring.DirectLimit.of R m i a = Ring.DirectLimit.of R m k (m i k (leOfHom u) a) :=
          (Ring.DirectLimit.of_f (leOfHom u) a).symm
        _ = Ring.DirectLimit.of R m k (m j k (leOfHom v) b) := by rw [hu, hv, huv]
        _ = Ring.DirectLimit.of R m j b := Ring.DirectLimit.of_f (leOfHom v) b
    · intro y
      obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit ht y
      exact ⟨Ring.DirectLimit.of R m i a, (hφ i a).trans ha⟩
  exact (RingEquiv.ofBijective φ hbij).toCommRingCatIso

/-- Theorem 10.11 の帰着に用いる。filtered 余極限の p 冪ねじれは p で消え、
導来 p 完備化は離散な perfectoid 環である。 -/
theorem isIntegralPerfectoid_completedFilteredColimit (p : ℕ) [Fact p.Prime]
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (F : I ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i, IsIntegralPerfectoid (F.obj i) p) :
    IsIntegralPerfectoid (completionRing p c.pt) p ∧
      (∀ (x : c.pt) (n : ℕ), (p : c.pt)^n * x = 0 → (p : c.pt) * x = 0) ∧
      (∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat c.pt) i).obj
        ((derivedComplexCompletionFunctor c.pt (p : c.pt)).obj
          ((moduleObjectFunctor c.pt).obj (ModuleCat.of c.pt c.pt))))) := by
  obtain ⟨J, _, _, _, G, _⟩ := exists_final_directed_orderBot I
  let D := G ⋙ F
  let f (i j : J) (h : i ≤ j) := (D.map (homOfLE h)).hom
  let : DirectedSystem (fun i => D.obj i) (fun i j h => f i j h) :=
    { map_self := fun {i} x =>
        RingHom.congr_fun (congrArg (fun q : D.obj i ⟶ D.obj i => q.hom) (D.map_id i)) x
      map_map := fun {k j i} hij hjk x =>
        (RingHom.congr_fun (congrArg (fun q : D.obj i ⟶ D.obj k => q.hom)
          (D.map_comp (homOfLE hij) (homOfLE hjk))) x).symm }
  let L := CommRingCat.of (Ring.DirectLimit (fun j => D.obj j) (fun i j h => f i j h))
  let e := ringDirectLimitIso D f (fun _ _ _ => rfl) (c.whisker G)
    ((Functor.Final.isColimitWhiskerEquiv G c).symm hc)
  have hD (j : J) : IsIntegralPerfectoid (D.obj j) p := hF (G.obj j)
  have hL (n : ℕ) (x : L) (hx : (p : L) ^ n * x = 0) :
      (p : L) * x = 0 :=
    ringDirectLimit_p_power_torsion_bound_of_perfectoid (fun j => D.obj j) f p hD n x hx
  have ht (x : c.pt) (n : ℕ) (hx : (p : c.pt) ^ n * x = 0) : (p : c.pt) * x = 0 := by
    let r := e.symm.commRingCatIsoToRingEquiv
    apply r.injective
    simp only [map_mul, map_natCast, map_zero]
    apply hL n
    simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg r hx
  refine ⟨?_, ht, ?_⟩
  · let := principalCompletionCommRing L (p : L)
    let := principalCompletionAlgebra L (p : L)
    let b := boundedPrincipalCompletionAdicAlgEquiv L (p : L)
      ⟨1, fun n x hx => by simpa only [pow_one] using hL n x hx⟩
    exact isIntegralPerfectoid_of_ringEquiv p
      (b.toRingEquiv.symm.trans ((ringCompletionFunctor p).mapIso e).commRingCatIsoToRingEquiv)
      (isIntegralPerfectoid_adicCompletion_ringDirectLimit (fun j => D.obj j) f hD)
  · obtain ⟨hge, hle, _⟩ := completedUnit_pure_bounded_torsion c.pt (p : c.pt)
      ⟨1, fun n x hx => by simpa only [pow_one] using ht x n hx⟩
    intro i hi
    rcases lt_or_gt_of_ne hi with hi | hi
    · exact (DerivedCategory.isGE_iff _ _).mp hge i hi
    · exact (DerivedCategory.isLE_iff _ _).mp hle i hi

end SerrePositivity.BhattScholze.Perfectoidization.Derived

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Thm 10.11" (partial := component) "filtered 余極限への帰着、有限表示近似、perfectoid の余極限の完備化（BS-W13）。離散性の本体は A6・A7 待ち。E3 の欄は引き続き Inputs ／ 11-10 更新"] _root_.SerrePositivity.BhattScholze.Perfectoidization.Derived.isIntegralPerfectoid_completedFilteredColimit
