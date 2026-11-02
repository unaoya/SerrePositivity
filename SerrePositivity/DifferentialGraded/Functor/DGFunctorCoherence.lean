module
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorEnrichment

/-! # 厳密 dg 関手の結合・単位と Hom end の等号移送
概要：元の dg 関手の結合・単位の等号と、その Hom end 上の移送を与える。
方針：全 Hom chain map の圏法則で関手を比較し、等号帰納で評価との交換を証明する。
規約：関手の対象作用を変更しない。使われ方：横合成の外側の結合・単位則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t s
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

/-- 元の厳密 dg 関手の合成は結合的。 -/
lemma strictDGFunctor_comp_assoc {A : Type u} [CommRing A]
    {C : Type v} [DGCategory A C] {D : Type w} [DGCategory A D]
    {E : Type t} [DGCategory A E] {B : Type s} [DGCategory A B]
    (F : DGFunctor A C D) (G : DGFunctor A D E) (H : DGFunctor A E B) :
    (F.comp G).comp H = F.comp (G.comp H) := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, eqToHom_refl,
    Category.comp_id, Category.assoc]

/-- 元の恒等 dg 関手による左単位則。 -/
lemma strictDGFunctor_id_comp {A : Type u} [CommRing A]
    {D : Type v} [DGCategory A D] {E : Type w} [DGCategory A E]
    (F : DGFunctor A D E) : (DGFunctor.id D).comp F = F := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [DGFunctor.comp, DGFunctor.id, EnrichedFunctor.comp_map, EnrichedFunctor.id_map,
    eqToHom_refl, Category.comp_id, Category.id_comp]

/-- 元の恒等 dg 関手による右単位則。 -/
lemma strictDGFunctor_comp_id {A : Type u} [CommRing A]
    {D : Type v} [DGCategory A D] {E : Type w} [DGCategory A E]
    (F : DGFunctor A D E) : F.comp (DGFunctor.id E) = F := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [DGFunctor.comp, DGFunctor.id, EnrichedFunctor.comp_map, EnrichedFunctor.id_map,
    eqToHom_refl, Category.comp_id]

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E]

/-- 元の dg 関手の等号による、同じ全次数 Hom end の移送。 -/
def dgFunctorHomTransport {M N M' N' : DGFunctor A D E} (hM : M = M') (hN : N = N') :
    dgFunctorHom A D E M N ⟶ dgFunctorHom A D E M' N' :=
  eqToHom (congrArg₂ (dgFunctorHom A D E) hM hN)

/-- Hom end の等号移送は、元の全対象評価の等号移送を回収する。 -/
@[reassoc]
lemma dgFunctorHomTransport_π {M N M' N' : DGFunctor A D E}
    (hM : M = M') (hN : N = N') (x : D) :
    dgFunctorHomTransport A D E hM hN ≫ dgFunctorHomπ A D E M' N' x =
      dgFunctorHomπ A D E M N x ≫ eqToHom
        (congrArg₂ (homObject A E) (congrArg (fun F => F.obj x) hM)
          (congrArg (fun F => F.obj x) hN)) := by
  cases hM
  cases hN
  simp only [dgFunctorHomTransport, eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 斉次元の等号移送は、元の対象評価の等号移送と可換。 -/
lemma dgFunctorHomTransport_apply_π {M N M' N' : DGFunctor A D E}
    (hM : M = M') (hN : N = N') {n : ℤ} (a : (dgFunctorHom A D E M N).X n) (x : D) :
    (dgFunctorHomπ A D E M' N' x).f n ((dgFunctorHomTransport A D E hM hN).f n a) =
      (eqToHom (congrArg₂ (homObject A E) (congrArg (fun F => F.obj x) hM)
        (congrArg (fun F => F.obj x) hN))).f n ((dgFunctorHomπ A D E M N x).f n a) :=
  congrArg (fun k => k.f n a) (dgFunctorHomTransport_π A D E hM hN x)

end SerrePositivity.KST.SConstruction
