module

public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：異なる端点表示を持つ三つの同型の像が同じ恒等射なら、その逆を含む積も恒等。
方針：Arrow の等式から端点を輸送し、合成と逆の通常の法則へ戻す。
規約：各因子の像の等式を要求する。使われ方：初期 Hom の三比較の評価の相殺。
-/

@[expose] public section
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 型付き端点の表示が異なっても、二つの Arrow の等式から積の等式を得る。 -/
lemma arrowComposition_congr {C : Type*} [Category* C] {a b c a' b' c' : C}
    {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'} {g' : b' ⟶ c'}
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hf
  subst a' b'
  obtain ⟨_, hc, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  subst c'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  subst f' g'
  rfl

/-- 同型の順方向の射が同じ Arrow なら、逆の射も同じ Arrow である。 -/
lemma arrowIsoInverse_congr {C : Type*} [Category* C] {a b a' b' : C}
    (I : a ≅ b) (J : a' ≅ b') (h : Arrow.mk I.hom = Arrow.mk J.hom) :
    Arrow.mk I.inv = Arrow.mk J.inv := by
  obtain ⟨ha, hb, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  subst a' b'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  have he : I = J := Iso.ext h
  subst J
  rfl

/-- 二因子の像が同じ恒等射なら、その同じ積の関手像も恒等射である。 -/
lemma functor_twoFactors_identity_arrow {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {a b c : C} (I : a ≅ b) (J : b ≅ c) (z : D)
    (hI : Arrow.mk (F.map I.hom) = Arrow.mk (𝟙 z))
    (hJ : Arrow.mk (F.map J.hom) = Arrow.mk (𝟙 z)) :
    Arrow.mk (F.map (I ≪≫ J).hom) = Arrow.mk (𝟙 z) := by
  simpa only [Iso.trans_hom, Functor.map_comp, Category.id_comp] using
    arrowComposition_congr hI hJ

/-- 三つの像が同じ恒等射なら、最初の逆と残りの積も同じ恒等射。 -/
lemma iso_threeFactors_identity_arrow {C : Type*} [Category* C] {a b c d : C}
    (I : a ≅ b) (J : a ≅ c) (K : c ≅ d) (z : C)
    (hI : Arrow.mk I.hom = Arrow.mk (𝟙 z))
    (hJ : Arrow.mk J.hom = Arrow.mk (𝟙 z))
    (hK : Arrow.mk K.hom = Arrow.mk (𝟙 z)) :
    Arrow.mk (I.symm ≪≫ J ≪≫ K).hom = Arrow.mk (𝟙 z) := by
  have hi := arrowIsoInverse_congr I (Iso.refl z) hI
  simpa only [Iso.refl_inv, Iso.trans_hom, Iso.symm_hom, Category.id_comp] using
    arrowComposition_congr hi (arrowComposition_congr hJ hK)

/-- 三つの同型の関手像の恒等性は、最初の逆を含む同じ積の像でも成立する。 -/
lemma functor_threeFactors_identity_arrow {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {a b c d : C} (I : a ≅ b) (J : a ≅ c) (K : c ≅ d) (z : D)
    (hI : Arrow.mk (F.map I.hom) = Arrow.mk (𝟙 z))
    (hJ : Arrow.mk (F.map J.hom) = Arrow.mk (𝟙 z))
    (hK : Arrow.mk (F.map K.hom) = Arrow.mk (𝟙 z)) :
    Arrow.mk (F.map (I.symm ≪≫ J ≪≫ K).hom) = Arrow.mk (𝟙 z) := by
  have h := iso_threeFactors_identity_arrow (F.mapIso I) (F.mapIso J) (F.mapIso K) z hI hJ hK
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp] using h

/-- 最初の二つが同じ恒等射なら、三因子の積の射は第三因子と同じ Arrow である。 -/
lemma iso_threeFactors_first_two_identity_arrow {C : Type*} [Category* C] {a b c d : C}
    (I : a ≅ b) (J : a ≅ c) (K : c ≅ d) (z : C)
    (hI : Arrow.mk I.hom = Arrow.mk (𝟙 z))
    (hJ : Arrow.mk J.hom = Arrow.mk (𝟙 z)) :
    Arrow.mk (I.symm ≪≫ J ≪≫ K).hom = Arrow.mk K.hom := by
  obtain ⟨ha, hb, hI⟩ := (Arrow.mk_eq_mk_iff _ _).mp hI
  subst z b
  obtain ⟨_, hc, hJ⟩ := (Arrow.mk_eq_mk_iff _ _).mp hJ
  subst c
  simp only [eqToHom_refl, Category.comp_id] at hI hJ
  have hi : I = Iso.refl a := Iso.ext hI
  have hj : J = Iso.refl a := Iso.ext hJ
  subst I J
  simp

/-- 関手像の最初の二つが同じ恒等射なら、積の像は第三因子の像と一致する。 -/
lemma functor_threeFactors_first_two_identity_arrow
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {a b c d : C}
    (I : a ≅ b) (J : a ≅ c) (K : c ≅ d) (z : D)
    (hI : Arrow.mk (F.map I.hom) = Arrow.mk (𝟙 z))
    (hJ : Arrow.mk (F.map J.hom) = Arrow.mk (𝟙 z)) :
    Arrow.mk (F.map (I.symm ≪≫ J ≪≫ K).hom) = Arrow.mk (F.map K.hom) := by
  have h := iso_threeFactors_first_two_identity_arrow
    (F.mapIso I) (F.mapIso J) (F.mapIso K) z hI hJ
  simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp] using h

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
