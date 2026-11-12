module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorGeneratorHomComponents
public import SerrePositivity.KST.SConstruction.DGHomGluingFunctor
/-!
概要：元の dg 代数四角形の自由対象での、指定単位比較を持つ実対角関手。
方針：元の四射の可換式を全 Hom 自然性へ移し、既存の Hom gluing 関手を適用する。
規約：左右の代数射と角の単位閉元を保持する。
使われ方：Milnor 比較の自由対象 Hom と元の対角作用の照合に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
open KST.SConstruction KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left
local notation "D" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.top
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.side
lemma dgGluingMilnorAlgebraDiagonal_naturality (x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source) :
    ((L).comp (p)).map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) ((p).obj ((L).obj x)))
        (𝟙 (ForgetEnrichment.of (Complex R) ((p).obj ((L).obj y)))) =
    ((G).comp (q)).map x y ≫
      eHomWhiskerRight (Complex R)
        (𝟙 (ForgetEnrichment.of (Complex R) ((q).obj ((G).obj x))))
        (ForgetEnrichment.of (Complex R) ((q).obj ((G).obj y))) := by
  erw [eHomWhiskerLeft_id (Complex R) («C» := ClosedCategory R (E)),
    eHomWhiskerRight_id (Complex R) («C» := ClosedCategory R (E)),
    Category.comp_id, Category.comp_id]
  exact congrArg Mon.Hom.hom d.commutes
def dgGluingMilnorAlgebraDiagonal :
    DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorGeneratorCategory R d) :=
  dgHomGluingFunctor R (C) (D) (E) (p) (q) (L) (G)
    (fun _ => 𝟙 _) (dgGluingMilnorAlgebraDiagonal_naturality R d)
lemma dgGluingMilnorAlgebraDiagonal_obj (x : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source) :
    (dgGluingMilnorAlgebraDiagonal R d).obj x = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingMilnorGenerator R d := rfl
lemma dgGluingMilnorAlgebraDiagonal_left :
    (dgGluingMilnorAlgebraDiagonal R d).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingLeft R (C) (D) (dgHomGluingBimodule R (C) (D) (E) (p) (q))) = L :=
  dgHomGluingFunctor_left R (C) (D) (E) (p) (q) (L) (G) _ _
lemma dgGluingMilnorAlgebraDiagonal_right :
    (dgGluingMilnorAlgebraDiagonal R d).comp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRight R (C) (D) (dgHomGluingBimodule R (C) (D) (E) (p) (q))) = G :=
  dgHomGluingFunctor_right R (C) (D) (E) (p) (q) (L) (G) _ _
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
