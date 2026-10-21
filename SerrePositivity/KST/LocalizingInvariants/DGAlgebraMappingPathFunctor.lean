module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathMapLaws
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：元の矢印全体に対する実 mapping-path 関手と、自然な因子分解を供給する。
方針：実可換正方形の射と厳密な関手則を、矢印圏上の関手へ束ねる。
規約：source と target を元の射から変更しない。使われ方：塔の functorial 置換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.MappingPath
variable (R : Type u) [CommRing R]

def functor : Arrow (Mon (Complex R)) ⥤ Mon (Complex R) where
  obj f := algebra R f.hom
  map {f g} s := map R f.hom g.hom s.left s.right (Arrow.w s).symm
  map_id f := map_id R f.hom
  map_comp {f g h} s t := map_comp R f.hom g.hom h.hom
    s.left s.right (Arrow.w s).symm t.left t.right (Arrow.w t).symm

def projectionNatTrans : functor R ⟶ Arrow.leftFunc where
  app f := projection R f.hom
  naturality _ _ s := map_projection R _ _ _ _ (Arrow.w s).symm

def sectionNatTrans : Arrow.leftFunc ⟶ functor R where
  app f := section_ R f.hom
  naturality _ _ s := (section_map R _ _ _ _ (Arrow.w s).symm).symm

def targetNatTrans : functor R ⟶ Arrow.rightFunc where
  app f := target R f.hom
  naturality _ _ s := map_target R _ _ _ _ (Arrow.w s).symm

lemma sectionNatTrans_projection : sectionNatTrans R ≫ projectionNatTrans R = 𝟙 _ := by
  apply NatTrans.ext
  funext f
  exact section_projection R f.hom

lemma sectionNatTrans_target : sectionNatTrans R ≫ targetNatTrans R = Arrow.leftToRight := by
  apply NatTrans.ext
  funext f
  exact section_target R f.hom

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.MappingPath
