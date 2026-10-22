module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomComplex
public import SerrePositivity.InfinityCategories.Derived.ComplexMinusOneCochainBoundary

/-!
gluing Hom の全次数の微分式と、全パラメータからの射の一意性。
次数 −1 の比較成分を落とさず、二射影と合わせて実射を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomComplex
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)
  (X Y : DGGluingObject R C D M)

/-- 全 Hom の微分を左射影すると、元の左 Hom の微分を得る。 -/
lemma dgGluingHom_d_left (n : ℤ) :
    (dgGluingHomComplex R C D M X Y).d n (n + 1) ≫
      (dgGluingLeftHomMap R C D M X Y).f (n + 1) =
    (dgGluingLeftHomMap R C D M X Y).f n ≫
      (homObject R C X.left Y.left).d n (n + 1) :=
  ((dgGluingLeftHomMap R C D M X Y).comm n (n + 1)).symm

/-- 全 Hom の微分を右射影しても元の右 Hom の微分を得る。 -/
lemma dgGluingHom_d_right (n : ℤ) :
    (dgGluingHomComplex R C D M X Y).d n (n + 1) ≫
      (dgGluingRightHomMap R C D M X Y).f (n + 1) =
    (dgGluingRightHomMap R C D M X Y).f n ≫
      (homObject R D X.right Y.right).d n (n + 1) :=
  ((dgGluingRightHomMap R C D M X Y).comm n (n + 1)).symm

/-- 全整数次数で、比較成分の微分は −dh − (gμ − νf)。 -/
lemma dgGluingHom_d_comparison (n : ℤ) :
    (dgGluingHomPrimitive R C D M X Y).v n (n - 1) (by omega) ≫
      (M.value X.left Y.right).d (n - 1) n +
    (dgGluingHomComplex R C D M X Y).d n (n + 1) ≫
      (dgGluingHomPrimitive R C D M X Y).v (n + 1) n (by omega) +
    (dgGluingRightHomMap R C D M X Y ≫ dgGluingRightAction R C D M X Y -
      dgGluingLeftHomMap R C D M X Y ≫ dgGluingLeftAction R C D M X Y).f n = 0 := by
  have h := complexMinusOneCochain_boundary_v
    (dgGluingHomPrimitive R C D M X Y) _
    (dgGluingHomPrimitive_boundary R C D M X Y) n
  simpa only [dgGluingDifference, dgGluingRightHomMap, dgGluingLeftHomMap,
    Preadditive.comp_sub, Category.assoc] using h

variable (K : Complex R)
/-- 任意パラメータからの射の、次数 −1 の比較 cochain。 -/
def dgGluingHomComparison (f : K ⟶ dgGluingHomComplex R C D M X Y) :
    Cochain K (M.value X.left Y.right) (-1) :=
  (Cochain.ofHom f).comp (dgGluingHomPrimitive R C D M X Y) (zero_add _)

/-- 二射影と比較 cochain は全パラメータ複体からの実射を一意に決める。 -/
lemma dgGluingHom_ext (f g : K ⟶ dgGluingHomComplex R C D M X Y)
    (ha : f ≫ dgGluingLeftHomMap R C D M X Y = g ≫ dgGluingLeftHomMap R C D M X Y)
    (hb : f ≫ dgGluingRightHomMap R C D M X Y = g ≫ dgGluingRightHomMap R C D M X Y)
    (hh : dgGluingHomComparison R C D M X Y K f = dgGluingHomComparison R C D M X Y K g) :
    f = g := by
  have hp : f ≫ mappingCocone.fst (dgGluingDifference R C D M X Y) =
      g ≫ mappingCocone.fst (dgGluingDifference R C D M X Y) := by
    apply biprod.hom_ext
    · exact ha
    · exact hb
  apply HomologicalComplex.hom_ext
  intro n
  apply complexMappingCocone_X_ext (dgGluingDifference R C D M X Y) n
  · exact congrArg (fun t ↦ t.f n) hp
  · have hn := congrArg (fun t : Cochain K (M.value X.left Y.right) (-1) ↦
        t.v n (n - 1) (by omega)) hh
    simpa only [dgGluingHomComparison, dgGluingHomPrimitive,
      Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using hn

variable (a : K ⟶ homObject R C X.left Y.left) (b : K ⟶ homObject R D X.right Y.right)
  (h : Cochain K (M.value X.left Y.right) (-1))
  (hh : δ (-1) 0 h + Cochain.ofHom
    (biprod.lift a b ≫ dgGluingDifference R C D M X Y) = 0)

/-- 指定された比較ホモトピーも持ち上げから厳密に回収される。 -/
lemma dgGluingHomLift_comparison :
    dgGluingHomComparison R C D M X Y K (dgGluingHomLift R C D M X Y K a b h hh) = h := by
  apply Cochain.ext
  intro p q hpq
  simp only [dgGluingHomComparison, dgGluingHomPrimitive, Cochain.zero_cochain_comp_v,
    Cochain.ofHom_v, dgGluingHomLift]
  exact mappingCocone.lift_f_snd_v (dgGluingDifference R C D M X Y)
    (biprod.lift a b) h hh p q hpq

/-- 二射と比較ホモトピーの同じ指定値を持つ射は、構成した持ち上げだけである。 -/
lemma dgGluingHomLift_unique (f : K ⟶ dgGluingHomComplex R C D M X Y)
    (ha : f ≫ dgGluingLeftHomMap R C D M X Y = a)
    (hb : f ≫ dgGluingRightHomMap R C D M X Y = b)
    (ht : dgGluingHomComparison R C D M X Y K f = h) :
    f = dgGluingHomLift R C D M X Y K a b h hh := by
  apply dgGluingHom_ext R C D M X Y K
  · rw [ha, dgGluingHomLift_left]
  · rw [hb, dgGluingHomLift_right]
  · rw [ht, dgGluingHomLift_comparison]

end SerrePositivity.InfinityCategories
