module

public import SerrePositivity.AlgebraicGeometry.FiniteIdealColimitMembership

/-!
概要：filtered colimit での有限生成イデアルの包含・等式を共通の後段へ降ろす。
方針：有限生成元の所属を有限段へ移し、IsFiltered.span で有限個の条件をそろえる。
規約：Stacks 0B8W (3) のアフィンの比較。底変換の忠実平坦性は仮定しない。
使われ方：C03 の有限型イデアル層の局所模型を重なりで貼る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J] [IsFiltered J]

/-- colimit での有限個の所属を、同じ始点の一つの後段へ同時に降ろす。 -/
theorem exists_finset_ideal_map_mem_of_colimit_mem
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (i : J) (I : Ideal (F.obj i)) (s : Finset (F.obj i))
    (hs : ∀ x ∈ s, c.ι.app i x ∈ I.map (c.ι.app i).hom) :
    ∃ (j : J) (f : i ⟶ j), ∀ x ∈ s, F.map f x ∈ I.map (F.map f).hom := by
  classical
  revert hs
  induction s using Finset.induction_on with
  | empty => intro hs; exact ⟨i, 𝟙 i, by simp⟩
  | @insert x s hxs ih =>
    intro hs
    obtain ⟨j, f, hfx⟩ := exists_ideal_map_mem_of_colimit_mem F c hc i I x (hs x (by simp))
    obtain ⟨k, g, hgs⟩ := ih (fun y hy ↦ hs y (Finset.mem_insert_of_mem hy))
    obtain ⟨l, p, q, hpq⟩ := IsFiltered.span f g
    refine ⟨l, f ≫ p, ?_⟩
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · simpa only [Functor.map_comp, CommRingCat.comp_apply] using
        ideal_map_mem_functor_comp F f p I (F.map f z) hfx
    · rw [hpq]
      simpa only [Functor.map_comp, CommRingCat.comp_apply] using
        ideal_map_mem_functor_comp F g q I (F.map g z) (hgs z hz)

/-- 有限生成イデアルの colimit における像の包含は、同じ始点のある後段で成立する。 -/
theorem exists_ideal_map_le_of_colimit_map_le
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (i : J) (I K : Ideal (F.obj i)) (hI : I.FG)
    (hIK : I.map (c.ι.app i).hom ≤ K.map (c.ι.app i).hom) :
    ∃ (j : J) (f : i ⟶ j), I.map (F.map f).hom ≤ K.map (F.map f).hom := by
  classical
  obtain ⟨s, hs⟩ := hI
  have hmem : ∀ x ∈ s, c.ι.app i x ∈ K.map (c.ι.app i).hom := by
    intro x hx
    apply hIK
    apply Ideal.mem_map_of_mem
    rw [← hs]
    exact Ideal.subset_span hx
  obtain ⟨j, f, hf⟩ := exists_finset_ideal_map_mem_of_colimit_mem F c hc i K s hmem
  refine ⟨j, f, ?_⟩
  rw [← hs, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro y ⟨x, hx, rfl⟩
  exact hf x hx

/-- 同じ段の二つの有限生成イデアルが colimit で同じ像を持てば、ある後段で一致する。 -/
theorem exists_ideal_map_eq_of_colimit_map_eq
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (i : J) (I K : Ideal (F.obj i)) (hI : I.FG) (hK : K.FG)
    (hIK : I.map (c.ι.app i).hom = K.map (c.ι.app i).hom) :
    ∃ (j : J) (f : i ⟶ j), I.map (F.map f).hom = K.map (F.map f).hom := by
  obtain ⟨j, f, hf⟩ := exists_ideal_map_le_of_colimit_map_le F c hc i I K hI hIK.le
  obtain ⟨k, g, hg⟩ := exists_ideal_map_le_of_colimit_map_le F c hc i K I hK hIK.ge
  obtain ⟨l, p, q, hpq⟩ := IsFiltered.span f g
  refine ⟨l, f ≫ p, le_antisymm ?_ ?_⟩
  · have h := Ideal.map_mono (f := (F.map p).hom) hf
    simpa only [ideal_map_map_functor] using h
  · rw [hpq]
    have h := Ideal.map_mono (f := (F.map q).hom) hg
    simpa only [ideal_map_map_functor] using h

/-- 異なる二段の有限生成イデアルの像の等式を、二つの遷移射を持つ共通段へ降ろす。 -/
theorem exists_ideal_maps_eq_of_colimit_maps_eq
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (i j : J) (I : Ideal (F.obj i)) (K : Ideal (F.obj j)) (hI : I.FG) (hK : K.FG)
    (hIK : I.map (c.ι.app i).hom = K.map (c.ι.app j).hom) :
    ∃ (k : J) (f : i ⟶ k) (g : j ⟶ k), I.map (F.map f).hom = K.map (F.map g).hom := by
  let k := IsFiltered.max i j
  let f := IsFiltered.leftToMax i j
  let g := IsFiltered.rightToMax i j
  have hIc : (I.map (F.map f).hom).map (c.ι.app k).hom = I.map (c.ι.app i).hom := by
    rw [Ideal.map_map, ← CommRingCat.hom_comp, c.w f]
  have hKc : (K.map (F.map g).hom).map (c.ι.app k).hom = K.map (c.ι.app j).hom := by
    rw [Ideal.map_map, ← CommRingCat.hom_comp, c.w g]
  obtain ⟨l, h, heq⟩ := exists_ideal_map_eq_of_colimit_map_eq F c hc k
    (I.map (F.map f).hom) (K.map (F.map g).hom) (hI.map _) (hK.map _)
    (hIc.trans (hIK.trans hKc.symm))
  refine ⟨l, f ≫ h, g ≫ h, ?_⟩
  rw [← ideal_map_map_functor F f h I, ← ideal_map_map_functor F g h K]
  exact heq

end SerrePositivity.AlgebraicGeometry
