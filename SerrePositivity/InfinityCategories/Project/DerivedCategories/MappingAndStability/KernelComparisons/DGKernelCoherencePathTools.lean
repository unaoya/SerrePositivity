module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.KernelComparisons.DGKernelPostcompBimodule
/-!
概要：kernel の coherence で使う逆五角経路と dg 関手の単位合成。
方針：同型の逆合成則と、実 Hom 鎖写像の単位則を使う。
規約：元の指定射を保つ。使われ方：通常 kernel の五角経路の端点正規化。
-/
@[expose] public section
open CategoryTheory
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
/-- 同じ五角経路の等式を、逆二本と逆二本・順一本の経路へ反転する。 -/
lemma iso_inversePentagonPath {C : Type*} [Category C] {W X Y T Z : C}
    (a : W ≅ X) (b : X ≅ Z) (c : W ≅ Y) (d : Y ≅ T) (e : T ≅ Z)
    (h : a.hom ≫ b.hom = c.hom ≫ d.hom ≫ e.hom) :
    e.inv ≫ d.inv = b.inv ≫ a.inv ≫ c.hom := by
  have hi : a ≪≫ b = c ≪≫ d ≪≫ e := Iso.ext h
  have hh := congrArg (fun i : W ≅ Z => i.inv ≫ c.hom) hi
  simpa only [Iso.trans_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh.symm
open DifferentialGraded
/-- dg 関手の終域恒等との合成は、同じ全 Hom 鎖写像を持つ。 -/
lemma dgFunctor_comp_identity {R : Type*} [CommRing R] {C D : Type*}
    [DGCategory R C] [DGCategory R D] (F : DGFunctor R C D) :
    F.comp (DGFunctor.id D) = F := by
  apply EnrichedFunctor.ext (Complex R) (F := F.comp (DGFunctor.id D))
    (G := F) (fun _ => rfl)
  intro x y
  change (F.map x y ≫ 𝟙 _) ≫ 𝟙 _ = F.map x y
  simp only [Category.comp_id]
/-- dg 関手の始域恒等との合成は、同じ全 Hom 鎖写像を持つ。 -/
lemma dgFunctor_identity_comp {R : Type*} [CommRing R] {C D : Type*}
    [DGCategory R C] [DGCategory R D] (F : DGFunctor R C D) :
    (DGFunctor.id C).comp F = F := by
  apply EnrichedFunctor.ext (Complex R) (F := (DGFunctor.id C).comp F)
    (G := F) (fun _ => rfl)
  intro x y
  change (𝟙 _ ≫ F.map x y) ≫ 𝟙 _ = F.map x y
  simp only [Category.id_comp, Category.comp_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
