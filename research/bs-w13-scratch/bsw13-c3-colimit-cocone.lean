module

public import Mathlib.CategoryTheory.Presentable.Directed
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

private def ringDirectLimitCocone {J : Type u} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (F : J ⥤ CommRingCat.{u})
    (f : ∀ i j, i ≤ j → F.obj i →+* F.obj j)
    (hf : ∀ i j h, f i j h = (F.map (homOfLE h)).hom)
    [DirectedSystem (fun i => F.obj i) (fun i j h => f i j h)] : Cocone F where
  pt := CommRingCat.of (Ring.DirectLimit (fun i => F.obj i) (fun i j h => f i j h))
  ι :=
    { app := fun i => CommRingCat.ofHom
        (Ring.DirectLimit.of (fun i => F.obj i) (fun i j h => f i j h) i)
      naturality := by
        intro i j k
        apply CommRingCat.hom_ext
        ext x
        change Ring.DirectLimit.of (fun i => F.obj i) (fun i j h => f i j h) j ((F.map k).hom x) =
          Ring.DirectLimit.of (fun i => F.obj i) (fun i j h => f i j h) i x
        have hk : (F.map k).hom x = f i j (leOfHom k) x :=
          RingHom.congr_fun (hf i j (leOfHom k)).symm x
        rw [hk]
        exact Ring.DirectLimit.of_f (G := fun i => F.obj i) (f := fun i j h => f i j h)
          (leOfHom k) x }

set_option backward.isDefEq.respectTransparency false in
private def ringDirectLimitCoconeIso {J : Type u} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (F : J ⥤ CommRingCat.{u})
    (f : ∀ i j, i ≤ j → F.obj i →+* F.obj j)
    (hf : ∀ i j h, f i j h = (F.map (homOfLE h)).hom)
    [DirectedSystem (fun i => F.obj i) (fun i j h => f i j h)]
    (c : Cocone F) (hc : IsColimit c) : (ringDirectLimitCocone F f hf).pt ≅ c.pt := by
  let R (i : J) : Type u := F.obj i
  let m (i j : J) (h : i ≤ j) (x : R i) : R j := f i j h x
  let L := Ring.DirectLimit R m
  let d := ringDirectLimitCocone F f hf
  let φ : L →+* c.pt := Ring.DirectLimit.lift R m c.pt
    (fun i => (c.ι.app i).hom) (fun i j h x => by
      change (c.ι.app j).hom (f i j h x) = (c.ι.app i).hom x
      rw [hf]
      exact RingHom.congr_fun (congrArg (fun q : F.obj i ⟶ c.pt => q.hom) (c.w (homOfLE h))) x)
  have hφ (i : J) : φ.comp (Ring.DirectLimit.of R m i) = (c.ι.app i).hom :=
    RingHom.ext fun x => Ring.DirectLimit.lift_of (G := R) (f := m) c.pt _ _ i x
  let a : d.pt ⟶ c.pt := CommRingCat.ofHom φ
  let b : c.pt ⟶ d.pt := hc.desc d
  have ha (i : J) : d.ι.app i ≫ a = c.ι.app i := by
    apply CommRingCat.hom_ext
    change φ.comp (Ring.DirectLimit.of R m i) = _
    exact hφ i
  have hb (i : J) : c.ι.app i ≫ b = d.ι.app i := hc.fac d i
  refine ⟨a, b, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    change b.hom.comp φ = RingHom.id L
    apply Ring.DirectLimit.hom_ext
    intro i
    rw [RingHom.comp_assoc, hφ, RingHom.id_comp]
    exact congrArg (fun q : F.obj i ⟶ d.pt => q.hom) (hb i)
  · apply hc.hom_ext
    intro i
    rw [← Category.assoc, hb, ha, Category.comp_id]

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
  let L := ringDirectLimitCocone D f (fun _ _ _ => rfl)
  let e := ringDirectLimitCoconeIso D f (fun _ _ _ => rfl) (c.whisker G)
    ((Functor.Final.isColimitWhiskerEquiv G c).symm hc)
  have hD (j : J) : IsIntegralPerfectoid (D.obj j) p := hF (G.obj j)
  have hL (n : ℕ) (x : L.pt) (hx : (p : L.pt) ^ n * x = 0) :
      (p : L.pt) * x = 0 :=
    ringDirectLimit_p_power_torsion_bound_of_perfectoid (fun j => D.obj j) f p hD n x hx
  have ht (x : c.pt) (n : ℕ) (hx : (p : c.pt) ^ n * x = 0) : (p : c.pt) * x = 0 := by
    let r := e.symm.commRingCatIsoToRingEquiv
    apply r.injective
    simp only [map_mul, map_natCast, map_zero]
    apply hL n
    simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg r hx
  refine ⟨?_, ht, ?_⟩
  · let := principalCompletionCommRing L.pt (p : L.pt)
    let := principalCompletionAlgebra L.pt (p : L.pt)
    let b := boundedPrincipalCompletionAdicAlgEquiv L.pt (p : L.pt)
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
