module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMapLaws
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathHomotopy

/-!
概要：実経路代数を厳密な関手とし、両端評価と対角を自然変換へ束ねる。
方針：検証した実代数射の恒等・合成・自然性の等式をそのまま使う。
規約：一般の導来写像比較の完成は主張しない。使われ方：相対経路の実図式。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
variable (R : Type u) [CommRing R]

def functor : Mon (Complex R) ⥤ Mon (Complex R) where
  obj := algebra R
  map := map R
  map_id := map_id R
  map_comp := map_comp R

def sourceNatTrans : functor R ⟶ 𝟭 (Mon (Complex R)) where
  app := source R
  naturality _ _ f := map_source R f

def targetNatTrans : functor R ⟶ 𝟭 (Mon (Complex R)) where
  app := target R
  naturality _ _ f := map_target R f

def diagonalNatTrans : 𝟭 (Mon (Complex R)) ⟶ functor R where
  app := diagonal R
  naturality _ _ f := (diagonal_naturality R f).symm

lemma diagonalNatTrans_source : diagonalNatTrans R ≫ sourceNatTrans R = 𝟙 _ := by
  apply NatTrans.ext
  funext B
  exact diagonal_source R B

lemma diagonalNatTrans_target : diagonalNatTrans R ≫ targetNatTrans R = 𝟙 _ := by
  apply NatTrans.ext
  funext B
  exact diagonal_target R B

variable {R}

def Witness.postcomp {A B C : Mon (Complex R)} {f g : A ⟶ B}
    (h : Witness R f g) (a : B ⟶ C) : Witness R (f ≫ a) (g ≫ a) where
  hom := h.hom ≫ map R a
  source_eq := by rw [Category.assoc, map_source, ← Category.assoc, h.source_eq]
  target_eq := by rw [Category.assoc, map_target, ← Category.assoc, h.target_eq]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.Path
