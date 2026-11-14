module
public import SerrePositivity.DifferentialGraded.Module.Graded

/-! # 全次数 Yoneda 像の原始元の元の Hom への反映

概要：代表加群間の Hom end にある原始元を、元の dg Hom 複体へ厳密に戻す。
方針：Yoneda の Hom 鎖同型の逆の各次数を使い、微分との可換性で照合する。
規約：両次数は任意。使われ方：シフトを解いた原始元を元の dg 対象間で回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 鎖同型は、任意の二次数の具体的な原始元の存在を保存・反映する。 -/
lemma dgComplexIso_exists_primitive_iff {K L : Complex A} (φ : K ⟶ L) [IsIso φ]
    (k n : ℤ) (a : K.X n) :
    (∃ h : L.X k, L.d k n h = φ.f n a) ↔ ∃ h : K.X k, K.d k n h = a := by
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨(inv φ).f k h, ?_⟩
    have hc := ConcreteCategory.congr_hom ((inv φ).comm k n) h
    change K.d k n ((inv φ).f k h) = (inv φ).f n (L.d k n h) at hc
    rw [hc, hh]
    have hi := congrArg (fun f => f.f n a) (IsIso.hom_inv_id φ)
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
      ModuleCat.comp_apply, ModuleCat.id_apply] using hi
  · rintro ⟨h, hh⟩
    refine ⟨φ.f k h, ?_⟩
    have hc := ConcreteCategory.congr_hom (φ.comm k n) h
    change L.d k n (φ.f k h) = φ.f n (K.d k n h) at hc
    rw [hc, hh]

variable (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 Hom end の Yoneda 像に対する原始元は、元の実 dg Hom の原始元と同値。 -/
lemma dgYoneda_exists_gradedPrimitive_iff (x y : D) (k n : ℤ) (a : GradedHom A x y n) :
    (∃ h : (moduleHom A D (representable A x) (representable A y)).X k,
      (moduleHom A D (representable A x) (representable A y)).d k n h =
        (yonedaHom A D x y).f n a) ↔
      ∃ h : GradedHom A x y k, (homObject A D x y).d k n h = a := by
  let : IsIso (yonedaHom A D x y) := by
    unfold yonedaHom
    infer_instance
  exact dgComplexIso_exists_primitive_iff A (yonedaHom A D x y) k n a

end SerrePositivity.InfinityCategories.Project.DerivedCategories
