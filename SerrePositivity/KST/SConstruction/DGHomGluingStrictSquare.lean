module
public import SerrePositivity.KST.SConstruction.DGHomGluingFunctor

/-! # 元の厳密可換 dg 四角形の標準対角
概要：厳密可換四角形の対象等号を使い、実 Hom gluing への標準対角を構成する。
方針：元の関手等号から全 Hom 自然な閉比較を作り、同じ gluing 関手へ渡す。
規約：対角の存在や関手法則を仮定しない。使われ方：Milnor 四角形の生成元の像。
-/
@[expose] public section
noncomputable section
universe u v w z t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

/-- 元の dg 関手等号が定める、同じ閉零対象等号移送。 -/
def dgFunctorEqClosedComponent {R : Type u} [CommRing R]
    {P : Type v} [DGCategory R P] {E : Type w} [DGCategory R E]
    (F G : DGFunctor R P E) (h : F = G) (x : P) :
    ForgetEnrichment.of (Complex R) (F.obj x) ⟶
      ForgetEnrichment.of (Complex R) (G.obj x) :=
  eqToHom (congrArg (fun H : DGFunctor R P E =>
    ForgetEnrichment.of (Complex R) (H.obj x)) h)

/-- 同じ dg 関手等号からの対象等号移送は、全 Hom 上で自然。 -/
lemma dgFunctorEq_closed_naturality {R : Type u} [CommRing R]
    {P : Type v} [DGCategory R P] {E : Type w} [DGCategory R E]
    (F G : DGFunctor R P E) (h : F = G) (x y : P) :
    F.map x y ≫ eHomWhiskerLeft (Complex R)
      (ForgetEnrichment.of (Complex R) (F.obj x)) (dgFunctorEqClosedComponent F G h y) =
    G.map x y ≫ eHomWhiskerRight (Complex R) (dgFunctorEqClosedComponent F G h x)
      (ForgetEnrichment.of (Complex R) (G.obj y)) := by
  cases h
  exact (congrArg (fun k => F.map x y ≫ k)
    (eHomWhiskerLeft_id (Complex R) (C := ClosedCategory R E)
      (ForgetEnrichment.of (Complex R) (F.obj x))
      (ForgetEnrichment.of (Complex R) (F.obj y)))).trans
    (congrArg (fun k => F.map x y ≫ k)
      (eHomWhiskerRight_id (Complex R) (C := ClosedCategory R E)
        (ForgetEnrichment.of (Complex R) (F.obj x))
        (ForgetEnrichment.of (Complex R) (F.obj y)))).symm

variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (E : Type z) [DGCategory R E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  {P : Type t} [DGCategory R P] (L : DGFunctor R P C) (G : DGFunctor R P D)
  (h : L.comp p = G.comp q)

/-- 元の厳密可換 dg 四角形の、同じ対象等号からの閉比較。 -/
def dgStrictSquareClosedComparison (x : P) :
    ForgetEnrichment.of (Complex R) (p.obj (L.obj x)) ⟶
      ForgetEnrichment.of (Complex R) (q.obj (G.obj x)) :=
  dgFunctorEqClosedComponent (L.comp p) (G.comp q) h x

/-- 元の厳密可換四角形から、実 Hom gluing への標準 dg 対角。 -/
def dgStrictSquareDiagonal :
    DGFunctor R P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D (dgHomGluingBimodule R C D E p q)) :=
  dgHomGluingFunctor R C D E p q L G (dgStrictSquareClosedComparison R C D E p q L G h)
    (dgFunctorEq_closed_naturality (L.comp p) (G.comp q) h)

/-- 同じ標準対角の左射影は、元の四角形の左関手そのもの。 -/
lemma dgStrictSquareDiagonal_left :
    (dgStrictSquareDiagonal R C D E p q L G h).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R C D (dgHomGluingBimodule R C D E p q)) = L :=
  dgHomGluingFunctor_left R C D E p q L G (dgStrictSquareClosedComparison R C D E p q L G h)
    (dgFunctorEq_closed_naturality (L.comp p) (G.comp q) h)

/-- 同じ標準対角の右射影は、元の四角形の右関手そのもの。 -/
lemma dgStrictSquareDiagonal_right :
    (dgStrictSquareDiagonal R C D E p q L G h).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R C D (dgHomGluingBimodule R C D E p q)) = G :=
  dgHomGluingFunctor_right R C D E p q L G (dgStrictSquareClosedComparison R C D E p q L G h)
    (dgFunctorEq_closed_naturality (L.comp p) (G.comp q) h)

end SerrePositivity.KST.SConstruction
