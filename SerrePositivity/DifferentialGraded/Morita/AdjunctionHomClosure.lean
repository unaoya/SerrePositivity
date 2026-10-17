module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionHomTriangles
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedLocalizingGeneration

/-! # 右随伴のHom比較の同型・retract・余積閉性

## 概要
指定射L(R)→YによるHom全単射が成立する入力を、同型・retract・保存される余積で閉じる。

## 方針
retractの挿入射と射影射、余積の普遍性により比較の単射性と全射性を直接運ぶ。

## 規約と注意
随伴や比較の全入力での可逆性は仮定しない。余積保存を明示する。

## 使われ方
U16aの表現可能性の局所化帰納で用いる閉性補題。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits ZeroObject Preadditive Pretriangulated
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  [L.CommShift ℤ] [L.IsTriangulated]
  {R : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E} (r : L.obj R ⟶ Y)

omit [L.CommShift ℤ] [L.IsTriangulated] in
/-- Hom全単射は入力のretractへ制限できる。 -/
lemma brownHomComparison_retract {X Z : DerivedModuleCategory A D} (s : Retract X Z)
    (hZ : Function.Bijective (brownHomComparison A D E L r Z)) :
    Function.Bijective (brownHomComparison A D E L r X) := by
  constructor
  · intro f g h
    change L.map f ≫ r = L.map g ≫ r at h
    have he : s.r ≫ f = s.r ≫ g := by
      apply hZ.1
      change L.map (s.r ≫ f) ≫ r = L.map (s.r ≫ g) ≫ r
      rw [L.map_comp, L.map_comp, Category.assoc, Category.assoc, h]
    have he' := congrArg (fun k => s.i ≫ k) he
    simpa only [← Category.assoc, s.retract, Category.id_comp] using he'
  · intro f
    obtain ⟨g, hg⟩ := hZ.2 (L.map s.r ≫ f)
    change L.map g ≫ r = L.map s.r ≫ f at hg
    refine ⟨s.i ≫ g, ?_⟩
    change L.map (s.i ≫ g) ≫ r = f
    rw [L.map_comp, Category.assoc, hg, ← Category.assoc, ← L.map_comp,
      s.retract, L.map_id, Category.id_comp]

omit [L.CommShift ℤ] [L.IsTriangulated] in
/-- Hom全単射は入力の同型に沿って運べる。 -/
lemma brownHomComparison_iso {X Z : DerivedModuleCategory A D} (e : X ≅ Z)
    (hZ : Function.Bijective (brownHomComparison A D E L r Z)) :
    Function.Bijective (brownHomComparison A D E L r X) :=
  brownHomComparison_retract A D E L r (Retract.ofIso e) hZ

/-- 零対象を入力とするHom比較は全単射。 -/
lemma brownHomComparison_isZero {X : DerivedModuleCategory A D} (hX : IsZero X) :
    Function.Bijective (brownHomComparison A D E L r X) := by
  constructor
  · intro f g _
    exact hX.eq_of_src f g
  · intro f
    exact ⟨0, (L.map_isZero hX).eq_of_src _ _⟩

omit [L.CommShift ℤ] [L.IsTriangulated] in
/-- 保存される余積のHom比較は、各成分のHom全単射から全単射。 -/
lemma brownHomComparison_coproduct {J : Type z} [Small.{u} J]
    (F : J → DerivedModuleCategory A D)
    [PreservesColimit (Discrete.functor F) L]
    (hF : ∀ j, Function.Bijective (brownHomComparison A D E L r (F j))) :
    Function.Bijective (brownHomComparison A D E L r (∐ F)) := by
  constructor
  · intro f g h
    change L.map f ≫ r = L.map g ≫ r at h
    apply Sigma.hom_ext
    intro j
    apply (hF j).1
    change L.map (Sigma.ι F j ≫ f) ≫ r = L.map (Sigma.ι F j ≫ g) ≫ r
    rw [L.map_comp, L.map_comp, Category.assoc, Category.assoc, h]
  · intro f
    choose g hg using fun j => (hF j).2 (L.map (Sigma.ι F j) ≫ f)
    refine ⟨Sigma.desc g, ?_⟩
    apply (isColimitOfHasCoproductOfPreservesColimit L F).hom_ext
    rintro ⟨j⟩
    change L.map (Sigma.ι F j) ≫ (L.map (Sigma.desc g) ≫ r) = L.map (Sigma.ι F j) ≫ f
    rw [← L.map_comp_assoc, Sigma.ι_comp_desc]
    exact hg j

/-- 全整数shiftでHom比較が全単射となる入力の性質。 -/
def brownHomProperty : ObjectProperty (DerivedModuleCategory A D) :=
  fun X => ∀ n : ℤ, Function.Bijective (brownHomComparison A D E L r (X⟦n⟧))

omit [L.CommShift ℤ] [L.IsTriangulated] in
/-- Hom比較の性質は整数shiftで閉じる。 -/
lemma brownHomProperty_shift {X : DerivedModuleCategory A D}
    (hX : brownHomProperty A D E L r X) (a : ℤ) : brownHomProperty A D E L r (X⟦a⟧) := by
  intro b
  exact brownHomComparison_iso A D E L r ((shiftFunctorAdd _ a b).app X).symm (hX (a+b))

/-- Hom比較の性質は同型で閉じる。 -/
instance brownHomPropertyIsClosedUnderIsomorphisms :
    (brownHomProperty A D E L r).IsClosedUnderIsomorphisms where
  of_iso e hX n := brownHomComparison_iso A D E L r
    ((shiftFunctor _ n).mapIso e.symm) (hX n)

/-- Hom比較の性質はretractで閉じる。 -/
instance brownHomPropertyIsStableUnderRetracts :
    (brownHomProperty A D E L r).IsStableUnderRetracts where
  of_retract s hZ n := brownHomComparison_retract A D E L r (s.map (shiftFunctor _ n)) (hZ n)

/-- 全shiftのHom比較の全単射性は三角部分圏を定める。 -/
instance brownHomPropertyIsTriangulated : (brownHomProperty A D E L r).IsTriangulated where
  exists_zero := ⟨0, isZero_zero _, fun n =>
    brownHomComparison_isZero A D E L r ((shiftFunctor _ n).map_isZero (isZero_zero _))⟩
  toIsStableUnderShift := ⟨fun a => ⟨fun X hX => brownHomProperty_shift A D E L r hX a⟩⟩
  toIsTriangulatedClosed₂ := ObjectProperty.IsTriangulatedClosed₂.mk' (by
    intro T hT h1 h3 n
    apply brownHomComparison_triangle A D E L r _ (Triangle.shift_distinguished T hT n)
      (h1 n) (h3 n)
    · exact (brownHomProperty_shift A D E L r h1 n 1).2
    · exact (brownHomProperty_shift A D E L r h3 n (-1)).1)

end SerrePositivity.DifferentialGraded.Morita
