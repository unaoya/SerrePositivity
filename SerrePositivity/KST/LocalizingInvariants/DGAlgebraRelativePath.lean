module

public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackUniversal
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathFunctor
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMapSurjective

/-!
概要：代数射の上で定数となる実相対経路代数と、その両端評価を構成する。
方針：実経路関手と対角の代数的 pullback を使い、元の底への厳密な式を保つ。
規約：相対二端点射の準同型性は後続。使われ方：同じ底を持つ代数射の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
variable (R : Type u) [CommRing R] {C B : Mon (Complex R)} (p : C ⟶ B)

def algebra : Mon (Complex R) := MonoidPullback.obj (Path.map R p) (Path.diagonal R B)

def inclusion : algebra R p ⟶ Path.algebra R C :=
  MonoidPullback.fst (Path.map R p) (Path.diagonal R B)

def projection : algebra R p ⟶ B := MonoidPullback.snd (Path.map R p) (Path.diagonal R B)

lemma condition : inclusion R p ≫ Path.map R p = projection R p ≫ Path.diagonal R B :=
  MonoidPullback.condition _ _

def source : algebra R p ⟶ C := inclusion R p ≫ Path.source R C

def target : algebra R p ⟶ C := inclusion R p ≫ Path.target R C

@[reassoc]
lemma source_projection : source R p ≫ p = projection R p := by
  rw [source, Category.assoc, ← Path.map_source, ← Category.assoc, condition,
    Category.assoc, Path.diagonal_source, Category.comp_id]

@[reassoc]
lemma target_projection : target R p ≫ p = projection R p := by
  rw [target, Category.assoc, ← Path.map_target, ← Category.assoc, condition,
    Category.assoc, Path.diagonal_target, Category.comp_id]

def diagonal : C ⟶ algebra R p :=
  MonoidPullback.lift (Path.map R p) (Path.diagonal R B) (Path.diagonal R C) p
    (Path.diagonal_naturality R p)

@[reassoc]
lemma diagonal_inclusion : diagonal R p ≫ inclusion R p = Path.diagonal R C :=
  MonoidPullback.lift_fst _ _ _ _ _

@[reassoc]
lemma diagonal_projection : diagonal R p ≫ projection R p = p :=
  MonoidPullback.lift_snd _ _ _ _ _

lemma diagonal_source : diagonal R p ≫ source R p = 𝟙 C := by
  rw [source, ← Category.assoc, diagonal_inclusion, Path.diagonal_source]

lemma diagonal_target : diagonal R p ≫ target R p = 𝟙 C := by
  rw [target, ← Category.assoc, diagonal_inclusion, Path.diagonal_target]

def cone : Limits.PullbackCone (Path.map R p) (Path.diagonal R B) :=
  MonoidPullback.cone _ _

def isLimit : Limits.IsLimit (cone R p) := MonoidPullback.isLimit _ _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
