module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
概要：filtered colimit のイデアルの像への所属を、同じ図式の有限段へ渡す。
方針：生成イデアルの帰納法で有限段の代表を選び、underlying type の等式の有限段一致を使う。
規約：Stacks 0B8W (3) のアフィンの比較。イデアルの有限生成性はこの所属の段には不要。
使われ方：C03 の有限生成イデアルの包含・等式を共通の後段へ降ろす。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J] [IsFiltered J]

omit [IsFiltered J] in
/-- イデアルの像の合成は、同じ図式の合成射による像に一致する。 -/
theorem ideal_map_map_functor (F : J ⥤ CommRingCat.{u})
    {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (I : Ideal (F.obj i)) :
    (I.map (F.map f).hom).map (F.map g).hom = I.map (F.map (f ≫ g)).hom := by
  rw [Ideal.map_map, ← CommRingCat.hom_comp, ← F.map_comp]

omit [IsFiltered J] in
/-- 図式の一段のイデアルの像への所属を、合成した後段の像へ移す。 -/
theorem ideal_map_mem_functor_comp (F : J ⥤ CommRingCat.{u})
    {i j k : J} (f : i ⟶ j) (g : j ⟶ k) (I : Ideal (F.obj i))
    (y : F.obj j) (hy : y ∈ I.map (F.map f).hom) :
    F.map g y ∈ I.map (F.map (f ≫ g)).hom := by
  have h := Ideal.mem_map_of_mem (F.map g).hom hy
  simpa only [Ideal.map_map, ← CommRingCat.hom_comp, ← F.map_comp] using h

omit [IsFiltered J] in
private theorem finiteIdeal_cocone_apply_map (F : J ⥤ CommRingCat.{u}) (c : Cocone F)
    {i j : J} (f : i ⟶ j) (y : F.obj i) :
    c.ι.app j (F.map f y) = c.ι.app i y :=
  congrArg (fun q : F.obj i ⟶ c.pt ↦ q y) (c.w f)

/-- colimit のイデアルの像の各元を、有限段の同じイデアルの像の元で代表する。 -/
theorem exists_ideal_map_rep_of_colimit_mem
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (i : J) (I : Ideal (F.obj i)) (x : c.pt) (hx : x ∈ I.map (c.ι.app i).hom) :
    ∃ (j : J) (f : i ⟶ j) (y : F.obj j),
      y ∈ I.map (F.map f).hom ∧ c.ι.app j y = x := by
  classical
  let φ : F.obj i →+* c.pt := (c.ι.app i).hom
  change x ∈ Submodule.span c.pt (φ '' (I : Set (F.obj i))) at hx
  induction hx using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨y, hy, rfl⟩ := ha
    refine ⟨i, 𝟙 i, y, ?_, rfl⟩
    simpa only [F.map_id, CommRingCat.hom_id, Ideal.map_id, SetLike.mem_coe] using hy
  | zero => exact ⟨i, 𝟙 i, 0, Ideal.zero_mem _, map_zero _⟩
  | add a b ha hb iha ihb =>
    obtain ⟨j, f, y, hy, hya⟩ := iha
    obtain ⟨k, g, z, hz, hzb⟩ := ihb
    obtain ⟨l, p, q, hpq⟩ := IsFiltered.span f g
    have hy' := ideal_map_mem_functor_comp F f p I y hy
    have hz' : F.map q z ∈ I.map (F.map (f ≫ p)).hom := by
      rw [hpq]
      exact ideal_map_mem_functor_comp F g q I z hz
    refine ⟨l, f ≫ p, F.map p y + F.map q z, Ideal.add_mem _ hy' hz', ?_⟩
    rw [map_add, finiteIdeal_cocone_apply_map, finiteIdeal_cocone_apply_map, hya, hzb]
  | smul a x hx ih =>
    obtain ⟨j, f, y, hy, hyx⟩ := ih
    obtain ⟨k, z, hza⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves (forget CommRingCat) hc) a
    change c.ι.app k z = a at hza
    let p := IsFiltered.leftToMax j k
    let q := IsFiltered.rightToMax j k
    refine ⟨IsFiltered.max j k, f ≫ p, F.map q z * F.map p y,
      Ideal.mul_mem_left _ _ (ideal_map_mem_functor_comp F f p I y hy), ?_⟩
    rw [map_mul, finiteIdeal_cocone_apply_map, finiteIdeal_cocone_apply_map, hza, hyx,
      smul_eq_mul]

/-- colimit でのイデアルの像への所属は、同じ始点のある後段で成立する。 -/
theorem exists_ideal_map_mem_of_colimit_mem
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (i : J) (I : Ideal (F.obj i)) (x : F.obj i)
    (hx : c.ι.app i x ∈ I.map (c.ι.app i).hom) :
    ∃ (j : J) (f : i ⟶ j), F.map f x ∈ I.map (F.map f).hom := by
  obtain ⟨j, f, y, hy, hyx⟩ := exists_ideal_map_rep_of_colimit_mem F c hc i I _ hx
  have heq : c.ι.app j y = c.ι.app j (F.map f x) :=
    hyx.trans (finiteIdeal_cocone_apply_map F c f x).symm
  obtain ⟨k, g, hxy⟩ := (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (forget CommRingCat) hc) y (F.map f x)).mp heq
  refine ⟨k, f ≫ g, ?_⟩
  have hmem := ideal_map_mem_functor_comp F f g I y hy
  have heq' : F.map g y = F.map (f ≫ g) x := by simpa [Functor.map_comp] using hxy
  rw [heq'] at hmem
  exact hmem

end SerrePositivity.AlgebraicGeometry
